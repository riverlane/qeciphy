// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Evan Sun

//------------------------------------------------------------------------------
// QECIPHY Auto-Renegotiation Controller
//------------------------------------------------------------------------------
// This module restarts link establishment without ARSTn by generating an
// internal reset that re-runs the full reset sequence.
//
// Triggers (when enable_i is high):
// - Link drop: FAULT_FATAL with a FAW or CRC error code
// - Training timeout: link not ready for TRAINING_TIMEOUT cycles
// - FIFO overflows are not triggers and remain fatal until ARSTn
//
// Sequence: IDLE -> HOLDOFF -> ASSERT_RST -> IDLE
// - HOLDOFF lets the remote side detect the drop (local TX is off)
// - ASSERT_RST drives reneg_rst_n_o low (RST_CYCLES must span several FCLK cycles)
//
// Observability:
// - reneg_ecode_o latches ecode_i (NO_ERROR for a training timeout)
// - reneg_count_o and reneg_ecode_o are only cleared by ARSTn
//
// Must be reset by ARSTn only, never by reneg_rst_n_o.
//------------------------------------------------------------------------------

`include "qeciphy_pkg.sv"

module qeciphy_reneg_ctrl #(
    parameter int unsigned TRAINING_TIMEOUT = 16777216,  // Training timeout (clk_i cycles)
    parameter int unsigned HOLDOFF_CYCLES   = 1024,      // Delay before internal reset (clk_i cycles)
    parameter int unsigned RST_CYCLES       = 64         // Internal reset width (clk_i cycles)
) (
    input  logic       clk_i,          // Clock input (ACLK)
    input  logic       rst_n_i,        // Active-low reset (ARSTn only)
    input  logic       enable_i,       // Auto-renegotiation enable
    input  logic [3:0] status_i,       // Link status from qeciphy_controller
    input  logic       fault_fatal_i,  // Fatal fault from qeciphy_controller
    input  logic [3:0] ecode_i,        // Error code from qeciphy_error_handler
    output logic       reneg_rst_n_o,  // Internal reset request (active-low)
    output logic [7:0] reneg_count_o,  // Saturating renegotiation count
    output logic [3:0] reneg_ecode_o   // ECODE of most recent renegotiation
);

   localparam int TIMEOUT_W = $clog2(TRAINING_TIMEOUT + 1);
   localparam int DELAY_W = $clog2(((HOLDOFF_CYCLES > RST_CYCLES) ? HOLDOFF_CYCLES : RST_CYCLES) + 1);

   typedef enum logic [2:0] {
      IDLE       = 3'b001,  // Monitor for triggers
      HOLDOFF    = 3'b010,  // Wait for remote side to detect the drop
      ASSERT_RST = 3'b100   // Internal reset asserted
   } fsm_t;

   fsm_t state, state_nxt;

   logic                 in_idle_state;
   logic                 in_holdoff_state;

   logic                 link_drop;  // FAW or CRC fault
   logic                 in_training;  // Link not ready and not faulted
   logic [TIMEOUT_W-1:0] training_counter;
   logic                 training_timeout;
   logic [  DELAY_W-1:0] delay_counter;
   logic                 holdoff_done;
   logic                 rst_done;
   logic                 reneg_start;

   logic                 reneg_rst_n;
   logic [          7:0] reneg_count;
   logic [          3:0] reneg_ecode;

   assign in_idle_state       = state[0];
   assign in_holdoff_state    = state[1];

   assign reneg_rst_n_o       = reneg_rst_n;
   assign reneg_count_o       = reneg_count;
   assign reneg_ecode_o       = reneg_ecode;

   // =========================================================================
   // Trigger Detection
   // =========================================================================

   assign link_drop = fault_fatal_i && (ecode_i == qeciphy_pkg::FAW_ERROR || ecode_i == qeciphy_pkg::CRC_ERROR);

   assign in_training = (status_i == qeciphy_pkg::WAIT_FOR_RESET) || (status_i == qeciphy_pkg::LINK_TRAINING) || (status_i == qeciphy_pkg::RX_LOCKED);

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         training_counter <= '0;
      end else if (!in_idle_state || !in_training) begin
         training_counter <= '0;
      end else if (!training_timeout) begin
         training_counter <= training_counter + TIMEOUT_W'(1);
      end
   end

   assign training_timeout = (training_counter == TIMEOUT_W'(TRAINING_TIMEOUT));

   assign reneg_start      = enable_i && in_idle_state && (link_drop || training_timeout);

   // =========================================================================
   // Holdoff / Reset Pulse Counter
   // =========================================================================

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         delay_counter <= '0;
      end else if (in_idle_state || (in_holdoff_state && holdoff_done)) begin
         delay_counter <= '0;
      end else begin
         delay_counter <= delay_counter + DELAY_W'(1);
      end
   end

   assign holdoff_done = (delay_counter == DELAY_W'(HOLDOFF_CYCLES - 1));
   assign rst_done     = (delay_counter == DELAY_W'(RST_CYCLES - 1));

   // =========================================================================
   // State Machine
   // =========================================================================

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         state <= IDLE;
      end else begin
         state <= state_nxt;
      end
   end

   always_comb begin
      case (state)
         IDLE:       state_nxt = reneg_start ? HOLDOFF : IDLE;
         HOLDOFF:    state_nxt = holdoff_done ? ASSERT_RST : HOLDOFF;
         ASSERT_RST: state_nxt = rst_done ? IDLE : ASSERT_RST;
         default:    state_nxt = IDLE;
      endcase
   end

   // Registered for a glitch-free reset
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         reneg_rst_n <= 1'b1;
      end else begin
         reneg_rst_n <= !(state_nxt == ASSERT_RST);
      end
   end

   // =========================================================================
   // Observability
   // =========================================================================

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         reneg_count <= '0;
      end else if (reneg_start && (reneg_count != 8'hFF)) begin
         reneg_count <= reneg_count + 8'd1;
      end
   end

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         reneg_ecode <= qeciphy_pkg::NO_ERROR;
      end else if (reneg_start) begin
         reneg_ecode <= ecode_i;  // NO_ERROR on training timeout
      end
   end

endmodule  // qeciphy_reneg_ctrl
