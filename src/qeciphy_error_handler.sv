// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// QECIPHY Error Handler
//------------------------------------------------------------------------------
// This module provides centralized error handling and reporting for QECIPHY.
// It collects error signals from various subsystems and generates 
// unified fault and error code outputs.
//
// Operation:
// - Monitors RX path faults, TX/RX FIFO overflow conditions
// - Implements priority-based error reporting with fault latching
// - Maps different error sources to standardized error codes
// - Provides fault_fatal output to the central controller
//
// Error Priority (highest to lowest):
// 1. RX fault fatal - passes through RX error code directly
// 2. TX FIFO overflow - maps to TX_FIFO_OVERFLOW error code  
// 3. RX FIFO overflow - maps to RX_FIFO_OVERFLOW error code
//
// Fault Latching:
// - fault_fatal_o latches high on any error condition
// - Only cleared by system reset
//------------------------------------------------------------------------------

`include "qeciphy_pkg.sv"

module qeciphy_error_handler (
    input  logic       clk_i,               // Clock input
    input  logic       rst_n_i,             // Active-low reset
    input  logic       rx_fault_fatal_i,    // RX subsystem fatal fault indicator
    input  logic [3:0] rx_error_code_i,     // RX subsystem error code
    input  logic       tx_fifo_overflow_i,  // TX FIFO overflow error indicator
    input  logic       rx_fifo_overflow_i,  // RX FIFO overflow error indicator
    output logic       fault_fatal_o,       // Latched fatal fault output
    output logic [3:0] ecode_o              // Latched error code output
);

   import qeciphy_pkg::*;
   
   qeciphy_error_t ecode;  // Internal error code using package enum type
   logic         fault_fatal;  // Internal fault fatal signal
   
   // Output assignments
   assign ecode_o = ecode;
    assign fault_fatal_o = fault_fatal;
   
   // Latch fault_fatal on any error condition, clear only on reset
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         fault_fatal <= 1'b0;  
      end else if (rx_fault_fatal_i || tx_fifo_overflow_i || rx_fifo_overflow_i) begin
         fault_fatal <= 1'b1; 
      end
   end

   
   // Priority-based error code assignment, latched until reset
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         ecode <= NO_ERROR;
      end else if (!fault_fatal && rx_fault_fatal_i) begin
         ecode <= qeciphy_error_t'(rx_error_code_i);  
      end else if (!fault_fatal && tx_fifo_overflow_i) begin
         ecode <= TX_FIFO_OVERFLOW;  
      end else if (!fault_fatal && rx_fifo_overflow_i) begin
         ecode <= RX_FIFO_OVERFLOW;  
      end
   end

endmodule  // qeciphy_error_handler
