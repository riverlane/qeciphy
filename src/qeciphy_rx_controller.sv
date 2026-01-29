// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// RX Controller
//------------------------------------------------------------------------------
// This module controls the overall RX path operation, managing state transitions
// from initialization through normal operation to fault handling.
//
// Operation:
// - Manages RX subsystem enable/disable based on global enable
// - Transitions through startup sequence: OFF -> TRAINING -> READY
// - Monitors for CRC and FAW errors during operation
// - Enters fatal fault state on any error during READY state
// - Provides status signals to higher-level controller
// - Outputs error codes corresponding to detected faults
// - Faults and error codes are sticky and require reset / disable to clear
//
// State Machine Flow:
// RESET -> OFF -> TRAINING -> READY -> [FAULT_FATAL on error]
//------------------------------------------------------------------------------

`include "qeciphy_pkg.sv"

module qeciphy_rx_controller (
    input logic clk_i,       // Clock input
    input logic rst_n_i,     // Active-low reset
    input logic enable_i,    // Global enable control
    input logic rx_locked_i, // RX boundary generator locked status

    // Error flags from RX monitoring
    input logic crc_err_i,  // CRC validation error (sticky)
    input logic faw_err_i,  // FAW validation error (sticky)

    // Outputs to qeciphy_rx_* modules
    output logic rx_enable_o,  // Enable signal for RX subsystem

    // Outputs to qeciphy_controller
    output logic       rx_rdy_o,          // RX ready for normal operation
    output logic       rx_fault_fatal_o,  // Fatal fault detected (sticky)
    output logic [3:0] rx_error_code_o    // RX error code output (sticky)
);

   import qeciphy_pkg::*;

   // State machine for RX subsystem control
   typedef enum logic [5:0] {
      RESET       = 6'b000001,  // Initial reset state
      OFF         = 6'b000010,  // Module disabled, awaiting enable
      TRAINING    = 6'b100100,  // Training phase, waiting for lock
      READY       = 6'b101000,  // Normal operation, monitoring for errors
      FAULT_FATAL = 6'b110000   // Error detected, requires reset / disable
   } fsm_t;

   fsm_t state, state_nxt;  // Current and next state variables
   logic in_training_ready_fault_state;  // Decodes TRAINING, READY or FAULT_FATAL state
   logic in_ready_state;  // Decodes READY state
   logic in_fault_state;  // Decodes FAULT_FATAL state
   qeciphy_error_t error_code;  // Error code

   // Output assignments from internal signals
   assign rx_rdy_o = in_ready_state;
   assign rx_fault_fatal_o = in_fault_state;
   assign rx_enable_o = in_training_ready_fault_state;
   assign rx_error_code_o = error_code;

   // State machine decoders for state detection
   assign in_training_ready_fault_state = state[5];
   assign in_ready_state = state[3];
   assign in_fault_state = state[4];

   // State machine register with enable override
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         state <= RESET;
      end else if (!enable_i) begin
         state <= OFF;  // Force to OFF when disabled
      end else begin
         state <= state_nxt;
      end
   end

   // Next-state logic
   always_comb begin
      unique case (state)
         RESET:       state_nxt = OFF;  // Always transition to OFF after reset
         OFF:         state_nxt = TRAINING;  // Begin training when enabled
         TRAINING:    state_nxt = (rx_locked_i ? READY : TRAINING);  // Wait for lock
         READY:       state_nxt = (crc_err_i || faw_err_i) ? FAULT_FATAL : READY;  // Monitor for errors
         FAULT_FATAL: state_nxt = FAULT_FATAL;  // Sticky fault state
         default:     state_nxt = RESET;
      endcase
   end

   // Error code logic
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         error_code <= NO_ERROR;  // Clear error code on reset
      end else if (!enable_i) begin
         error_code <= NO_ERROR;  // Clear error code on disable
      end else if (in_ready_state && crc_err_i) begin
         error_code <= CRC_ERROR;  // Set CRC error code
      end else if (in_ready_state && faw_err_i) begin
         error_code <= FAW_ERROR;  // Set FAW error code
      end
   end

endmodule
