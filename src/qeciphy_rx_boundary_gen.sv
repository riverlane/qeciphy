// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// RX Boundary Generator
//------------------------------------------------------------------------------
// This module performs frame alignment and generates timing boundaries for
// FAW (Frame Alignment Word) and CRC validation in the receive path.
//
// Operation:
// - Searches for FAW patterns in incoming data stream
// - Verifies alignment by detecting 7 consecutive valid FAWs
// - Generates faw_boundary_o signals every 64th clock cycles when locked
// - Generates crc_boundary_o signals every 7th clock cycles for CRC validation
// - Ensures that crc_boundary_o is deasserted until the first faw_boundary_o
// - Provides locked_o signal indicating successful frame alignment
// - Provides pass-through data path (tdata_i -> tdata_o)
//
// State Machine Flow:
// RESET -> DISABLED -> ALIGN -> CHECK -> LOCKED -> FAW_BOUNDARY_START -> CRC_BOUNDARY_START -> OPERATIONAL
//------------------------------------------------------------------------------

`include "qeciphy_pkg.sv"

module qeciphy_rx_boundary_gen (
    input  logic        clk_i,           // Clock input
    input  logic        rst_n_i,         // Active-low reset
    input  logic [63:0] tdata_i,         // Input data stream
    output logic [63:0] tdata_o,         // Output data stream (pass-through)
    input  logic        enable_i,        // Module enable control
    output logic        locked_o,        // Frame alignment locked status
    output logic        faw_boundary_o,  // FAW boundary timing signal
    output logic        crc_boundary_o   // CRC boundary timing signal
);

   import qeciphy_pkg::*;

   // State machine for frame alignment and boundary generation
   typedef enum bit [7:0] {
      RESET              = 8'b00000001,  // Initial reset state
      DISABLED           = 8'b00000010,  // Module disabled, awaiting enable
      ALIGN              = 8'b00000100,  // Searching for FAW pattern alignment
      CHECK              = 8'b00001000,  // Verifying alignment with multiple FAWs
      LOCKED             = 8'b00010000,  // Alignment verified
      FAW_BOUNDARY_START = 8'b00100000,  // Enable FAW boundary generation
      CRC_BOUNDARY_START = 8'b01000000,  // Enable CRC boundary generation
      OPERATIONAL        = 8'b10000000   // Fully operational, generating boundaries
   } fsm_t;

   fsm_t state, state_nxt;  // Current and next state variables

   logic [5:0] faw_counter;  // Counter for FAW boundary timing
   logic [5:0] faw_counter_nxt;  // Next value for faw_counter
   logic       faw_boundary;  // Internal FAW boundary signal

   logic [2:0] crc_counter;  // Counter for CRC boundary timing
   logic [2:0] crc_counter_nxt;  // Next value for crc_counter
   logic       crc_boundary;  // Internal CRC boundary signal

   logic [2:0] faw_check_counter;  // Counts consecutive valid FAWs
   logic       faw_check_done;  // Indicates 7 valid FAWs detected in CHECK state
   logic       faw_check_failed;  // Indicates FAW verification failure in CHECK state

   logic       faw_counter_realign;  // faw_counter realignment trigger
   logic       faw_alignment_done;  // Indicates faw_counter alignment done   

   logic       locked;  // Internal locked status register
   logic       faw_boundary_en;  // Enable for FAW boundary generation
   logic       crc_boundary_en;  // Enable for CRC boundary generation

   logic       faw_detected;  // FAW detection result
   logic       faw_detected_q;  // Registered FAW detection result

   logic       in_align_state;  // State decoder: in ALIGN state
   logic       in_check_state;  // State decoder: in CHECK state
   logic       in_locked_state;  // State decoder: in LOCKED state
   logic       in_faw_boundary_start_state;  // State decoder: in FAW_BOUNDARY_START state
   logic       in_crc_boundary_start_state;  // State decoder: in CRC_BOUNDARY_START state

   // Output assignments
   assign locked_o                    = locked;  // Locked status to external interface
   assign faw_boundary_o              = faw_boundary_en ? faw_boundary : 1'b0;  // Gated FAW boundary output
   assign crc_boundary_o              = crc_boundary_en ? crc_boundary : 1'b0;  // Gated CRC boundary output
   assign tdata_o                     = tdata_i;  // Pass-through data path

   // State machine decoders for individual state detection
   assign in_align_state              = state[2];
   assign in_check_state              = state[3];
   assign in_locked_state             = state[4];
   assign in_faw_boundary_start_state = state[5];
   assign in_crc_boundary_start_state = state[6];

   // Capture FAW detection result
   assign faw_detected                = enable_i ? is_faw(tdata_i) : 1'b0;

   // Register FAW detection result
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_detected_q <= 1'b0;
      end else begin
         faw_detected_q <= faw_detected;
      end
   end

   // State machine next-state logic
   always_comb begin
      unique case (state)
         RESET:              state_nxt = DISABLED;  // Always go to disabled after reset
         DISABLED:           state_nxt = ALIGN;  // Start alignment when enabled
         ALIGN:              state_nxt = faw_alignment_done ? CHECK : ALIGN;  // Move to check when aligned
         CHECK:              state_nxt = faw_check_failed ? ALIGN : faw_check_done ? LOCKED : CHECK;  // Verify. Jump to ALIGN on fail, LOCKED on success
         LOCKED:             state_nxt = FAW_BOUNDARY_START;  // Signal locked
         FAW_BOUNDARY_START: state_nxt = faw_boundary ? CRC_BOUNDARY_START : FAW_BOUNDARY_START;  // Begin FAW boundaries
         CRC_BOUNDARY_START: state_nxt = OPERATIONAL;  // Enable CRC boundaries after first FAW boundary
         OPERATIONAL:        state_nxt = OPERATIONAL;  // Stay operational
         default:            state_nxt = RESET;
      endcase
   end

   // State machine with enable override
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         state <= RESET;
      end else if (!enable_i) begin
         state <= DISABLED;  // Force to disabled when not enabled
      end else begin
         state <= state_nxt;
      end
   end

   // Generate realignment trigger when FAW detected during alignment
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_counter_realign <= 1'b0;
      end else begin
         faw_counter_realign <= in_align_state && faw_detected_q;
      end
   end

   // FAW alignment done: delayed one cycle from realignment trigger
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_alignment_done <= 1'b0;
      end else begin
         faw_alignment_done <= faw_counter_realign;
      end
   end

   // FAW counter: tracks position within 64-cycle frame
   assign faw_counter_nxt = faw_counter_realign ? 6'd2 : faw_counter + 6'd1;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_counter <= 6'd0;
      end else begin
         faw_counter <= faw_counter_nxt;
      end
   end

   // Generate FAW boundary signal every 64th cycle
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_boundary <= 1'b0;
      end else begin
         faw_boundary <= (faw_counter == 6'h3E);
      end
   end

   // CRC counter: tracks position within 7-cycle CRC frame
   assign crc_counter_nxt = (crc_boundary || faw_boundary) ? 3'd0 : crc_counter + 3'd1;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_counter <= 3'd0;
      end else begin
         crc_counter <= crc_counter_nxt;
      end
   end

   // Generate CRC boundary every 7th cycle
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_boundary <= 1'b0;
      end else begin
         crc_boundary <= (crc_counter == 3'h5);
      end
   end

   // FAW verification counter: counts consecutive valid FAWs during CHECK state
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_check_counter <= 3'd0;
      end else if (!enable_i) begin
         faw_check_counter <= 3'd0;
      end else if (in_check_state && faw_boundary && !faw_detected) begin
         faw_check_counter <= 3'd0;  // Reset on invalid FAW
      end else if (in_check_state && faw_boundary && faw_detected) begin
         faw_check_counter <= faw_check_counter + 3'h1;  // Increment on valid FAW
      end
   end

   // Generate failure signal on invalid FAW during CHECK state
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_check_failed <= 1'b0;
      end else begin
         faw_check_failed <= in_check_state && faw_boundary && !faw_detected;
      end
   end

   // Signal 7 consecutive FAWs verified in CHECK state
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_check_done <= 1'b0;
      end else if (!enable_i) begin
         faw_check_done <= 1'b0;
      end else if (&(faw_check_counter)) begin
         faw_check_done <= 1'b1;
      end
   end

   // Enable FAW boundary generation
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_boundary_en <= 1'b0;
      end else if (!enable_i) begin
         faw_boundary_en <= 1'b0;
      end else if (in_faw_boundary_start_state) begin
         faw_boundary_en <= 1'b1;  // Enable when FSM reaches FAW_BOUNDARY_START
      end
   end

   // Enable CRC boundary generation
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_boundary_en <= 1'b0;
      end else if (!enable_i) begin
         crc_boundary_en <= 1'b0;
      end else if (in_crc_boundary_start_state) begin
         crc_boundary_en <= 1'b1;  // Enable when FSM reaches CRC_BOUNDARY_START
      end
   end

   // Lock status: indicates frame alignment achieved
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         locked <= 1'b0;
      end else if (!enable_i) begin
         locked <= 1'b0;
      end else if (in_locked_state) begin
         locked <= 1'b1;
      end
   end

endmodule
