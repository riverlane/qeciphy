// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// RX 32-bit to 64-bit Data Width Converter with FAW Detection
//------------------------------------------------------------------------------
// This module converts 32-bit parallel data to 64-bit parallel data while
// automatically detecting the correct word alignment using Frame Alignment
// Word (FAW) pattern recognition.
//
// Operation:
// - Creates two possible 64-bit word alignments from incoming 32-bit data
// - Tests both alignments for valid FAW patterns
// - Automatically selects and locks onto the correct alignment
// - Provides alignment status output for downstream processing
//
// Alignment Strategy:
// - Combination 0: {current_32b_word, previous_32b_word}  
// - Combination 1: {previous_32b_word, older_32b_word}
// - This is to ensure that we don't miss FAW patterns because of varying clock
//   phase relationships between clk_2x_i and clk_i.
//
// State Machine: RESET -> SEARCH_ALIGNMENT -> CONFIRM_ALIGNMENT -> DONE
//------------------------------------------------------------------------------

`include "qeciphy_pkg.sv"

module qeciphy_rx_32b_to_64b (
    input  logic        clk_2x_i,     // 2x clock for 32-bit data capture
    input  logic        clk_i,        // 1x clock for 64-bit data output  
    input  logic        rst_n_i,      // Active-low reset
    input  logic [31:0] tdata_32b_i,  // 32-bit input data stream
    output logic [63:0] tdata_64b_o,  // 64-bit output data stream
    output logic        aligned_o     // Alignment status output
);

   import qeciphy_pkg::*;

   // State Machine Definition
   typedef enum bit [3:0] {
      RESET             = 4'b0001,  // Initial reset state
      SEARCH_ALIGNMENT  = 4'b0010,  // Search for FAW in both alignment options
      CONFIRM_ALIGNMENT = 4'b0100,  // Verify alignment stability
      DONE              = 4'b1000   // Alignment locked and stable
   } fsm_t;

   fsm_t state, state_nxt;  // Current and next state registers

   // Data Path Registers
   logic [31:0] tdata_32b_2x_q;  // Delayed 32-bit input (clk_2x_i domain)
   logic [63:0] tdata_64b_2x;  // 64-bit combination 0 (clk_2x_i domain)
   logic [63:0] tdata_64b_2x_q;  // 64-bit combination 1 (clk_2x_i domain) 
   logic [63:0] tdata_64b                                                  [0:1];  // Two alignment options in clk_i domain
   logic [63:0] tdata_64b_aligned;  // Selected aligned output data

   // Control and Status Signals  
   logic        option;  // Selected alignment option (0 or 1)
   logic [ 1:0] is_faw_q;  // FAW detection results for both options

   // State Machine Status Decoding
   logic        in_search_alignment_state;
   logic        in_confirm_alignment_state;
   logic        in_done_state;

   // Timeout Detection for Alignment Stability
   logic        timeout;  // Timeout flag indicating alignment instability
   logic [ 7:0] timeout_counter;  // Timeout counter
   logic [ 7:0] timeout_counter_nxt;  // Next counter value


   // State Machine Status Decoding
   assign in_search_alignment_state  = state[1];
   assign in_confirm_alignment_state = state[2];
   assign in_done_state              = state[3];

   // =========================================================================
   // 32-bit Data Capture and 64-bit Word Formation (clk_2x_i domain)
   // =========================================================================

   // Delay incoming 32-bit data by one clk_2x_i cycle
   always_ff @(posedge clk_2x_i) begin
      if (!rst_n_i) begin
         tdata_32b_2x_q <= '0;
      end else begin
         tdata_32b_2x_q <= tdata_32b_i;
      end
   end

   // Form current 64-bit combination 0: {current_32b, delayed_32b}
   assign tdata_64b_2x = {tdata_32b_i, tdata_32b_2x_q};

   // Delay the 64-bit combination in clk_2x_i domain to create combination 1
   always_ff @(posedge clk_2x_i) begin
      if (!rst_n_i) begin
         tdata_64b_2x_q <= '0;
      end else begin
         tdata_64b_2x_q <= tdata_64b_2x;
      end
   end

   // =========================================================================
   // Alignment Options (clk_i domain)
   // =========================================================================

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         tdata_64b[0] <= '0;
         tdata_64b[1] <= '0;
      end else begin
         tdata_64b[0] <= tdata_64b_2x;
         tdata_64b[1] <= tdata_64b_2x_q;
      end
   end

   // =========================================================================
   // Frame Alignment Word (FAW) Detection
   // =========================================================================

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         is_faw_q <= '0;
      end else begin
         is_faw_q[0] <= is_faw(tdata_64b[0]);  // Check option 0 for FAW
         is_faw_q[1] <= is_faw(tdata_64b[1]);  // Check option 1 for FAW
      end
   end

   // =========================================================================
   // Alignment Option Selection
   // =========================================================================

   // Defaults to option 0, switches to option 1 if FAW found there during search
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         option <= 1'b0;
      end else if (in_search_alignment_state && is_faw_q[1]) begin
         option <= 1'b1;
      end
   end

   // =========================================================================
   // Timeout Logic
   // =========================================================================

   // Count cycles during confirmation
   assign timeout_counter_nxt = in_confirm_alignment_state ? timeout_counter + 8'd1 : 8'd0;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         timeout_counter <= 8'd0;
      end else begin
         timeout_counter <= timeout_counter_nxt;
      end
   end

   // Timeout occurs when MSB is set (128+ cycles without FAW detection)
   assign timeout = timeout_counter[7];

   // =========================================================================
   // State Machine
   // =========================================================================

   // State register
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         state <= RESET;
      end else begin
         state <= state_nxt;
      end
   end

   // Next state logic
   always_comb begin
      case (state)
         RESET: state_nxt = SEARCH_ALIGNMENT;  // Start searching after reset is released
         SEARCH_ALIGNMENT: state_nxt = |is_faw_q ? CONFIRM_ALIGNMENT : SEARCH_ALIGNMENT;  // Move to confirm if FAW is detected in any option
         CONFIRM_ALIGNMENT: state_nxt = timeout ? SEARCH_ALIGNMENT : is_faw_q[option] ? DONE : CONFIRM_ALIGNMENT;  // Timeout: restart search, Stable FAW: lock alignment, else stay in confirm
         DONE: state_nxt = DONE;  // Stay locked once aligned
         default: state_nxt = RESET;  // Safety fallback to reset
      endcase
   end

   // =========================================================================
   // Outputs
   // =========================================================================

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         tdata_64b_aligned <= '0;
      end else begin
         tdata_64b_aligned <= tdata_64b[option];  // Select based on chosen option
      end
   end

   assign tdata_64b_o = tdata_64b_aligned;
   assign aligned_o   = in_done_state;

endmodule  // qeciphy_rx_32b_to_64b
