// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// RX Data Monitor
//------------------------------------------------------------------------------
// This module monitors received data for frame alignment and CRC validation,
// providing error-free data output.
//
// Operation:
// - Delays input data through a 11-stage pipeline while CRC validation occurs
// - Validates FAW during boundary cycles using packet format checker
// - Computes and validates CRCs for data integrity
// - Extracts remote receiver ready status from FAW
// - Gates output data based on error conditions
// - Valid pipeline populated from validation word during CRC boundary
// - Output only when no FAW or CRC errors detected
// - Enable signal allows global disable of monitoring
// - Error signals provide diagnostic information
//
// Timing Diagram (13 clock cycles showing the pipeline):
//
//                      +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+     
// clk_i                |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |     
//                   ---+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +---  
//                                                                                                       
//                   +--+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+  
// tdata_i           |  | CRC | D01 | D02 | D03 | D04 | D05 | D06 | CRC | D07 | D08 | D09 | D10 | D11 |  
//                   +--+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+  
//                                                                                                       
//                      +-----+                                   +-----+                                
// crc_boundary_i       |     |                                   |     |                                
//                   ---+     +-----------------------------------+     +------------------------------  
//                                                                                                       
//                                                                             3 cycles from CRC boundary
//                                                                                            |          
//                                        +-----+                                   +-----+<--+          
// crc_check_done                         |     |                                   |     |              
//                   ---------------------+     +-----------------------------------+     +------------  
//                                                                                                       
//                   +--------------------------------------------------------------------------+-----+  
// tdata_o           |                                                                          | D01 |  
//                   +--------------------------------------------------------------------------+-----+  
//                                                                                                    ^  
//                                                                                                    |  
//                                                                 Another 2 cycles from check_done --+  


`include "qeciphy_pkg.sv"

module qeciphy_rx_monitor (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic [63:0] tdata_i,
    output logic [63:0] tdata_o,
    output logic        tvalid_o,
    input  logic        enable_i,
    input  logic        faw_boundary_i,
    input  logic        crc_boundary_i,
    output logic        crc_error_o,
    output logic        faw_error_o,
    output logic        remote_rx_rdy_o
);

   qeciphy_pkg::qeciphy_faw_t        faw;  // Frame Alignment Word structure

   logic                             faw_error;  // FAW validation error (sticky)
   logic                             crc_error;  // CRC validation error (sticky)
   logic                             remote_rx_rdy;  // Remote receiver ready status
   logic                      [63:0] data_pipe                                                        [0:10];  // 11-stage data delay pipeline
   logic                      [10:0] valid_pipe;  // Valid bit pipeline (synchronized with data)
   logic                      [10:0] valid_pipe_nxt;  // Next state of valid pipeline

   logic                      [15:0] crc01_calc;  // Calculated CRC01 value
   logic                      [15:0] crc23_calc;  // Calculated CRC23 value
   logic                      [15:0] crc45_calc;  // Calculated CRC45 value
   logic                      [ 7:0] crcvw_calc;  // Calculated CRC VW value
   logic                             crc_valid;  // Valid signal for the calulated CRCs
   logic                             crc_check_error;  // CRC check error from qeciophy_crc_check
   logic                             crc_check_done;  // CRC check done signal from qeciophy_crc_check

   // Output assignments from pipeline head and status signals
   assign faw_error_o     = faw_error;
   assign crc_error_o     = crc_error;
   assign remote_rx_rdy_o = remote_rx_rdy;
   assign tdata_o         = data_pipe[0];  // Output from pipeline head
   assign tvalid_o        = valid_pipe[0];  // Valid from pipeline head

   // FAW error detection: sticky error when invalid FAW detected
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_error <= 1'b0;
      end else if (!enable_i) begin
         faw_error <= 1'b0;  // Clear when disabled
      end else if (faw_boundary_i && !qeciphy_pkg::is_faw(tdata_i)) begin
         faw_error <= 1'b1;  // Set on invalid FAW
      end
   end

   // FAW structure extraction (valid only during faw_boundary_i)
   assign faw = qeciphy_pkg::qeciphy_faw_t'(tdata_i);

   // Remote receiver ready extraction from FAW
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         remote_rx_rdy <= 1'b0;
      end else if (!enable_i) begin
         remote_rx_rdy <= 1'b0;  // Clear when disabled
      end else if (faw_boundary_i) begin
         remote_rx_rdy <= faw.rx_rdy;  // Extract from FAW
      end
   end

   // Data pipeline: 11-stage shift register for delaying output
   always_ff @(posedge clk_i) begin
      data_pipe[10] <= tdata_i;  // Input to pipeline tail
      for (int i = 1; i < 11; i++) begin
         data_pipe[i-1] <= data_pipe[i];  // Shift pipeline forward
      end
   end

   // Valid pipeline: tracks which data words are valid for output
   assign valid_pipe_nxt = !enable_i ? '0 :  // No valid data when disabled
       (faw_error || crc_error) ? '0 :  // Invalidate all remaining data on error
       crc_boundary_i ? {1'b0, tdata_i[13:8], valid_pipe[4:1]} :  // Load valid bits from validation word, insert 0 at MSB to account for the boundary
       {1'b0, valid_pipe[10:1]};  // Shift pipeline with 0 insertion

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         valid_pipe <= '0;
      end else begin
         valid_pipe <= valid_pipe_nxt;  // Update valid pipeline with next state
      end
   end

   // CRC error detection: sticky error when CRC check fails
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_error <= 1'b0;
      end else if (!enable_i) begin
         crc_error <= 1'b0;  // Clear when disabled
      end else if (crc_check_done && crc_check_error) begin
         crc_error <= 1'b1;  // Set on CRC validation failure
      end
   end

   // CRC computation module
   qeciphy_crc_compute i_crc_compute (
       .clk_i         (clk_i),
       .rst_n_i       (rst_n_i),
       .faw_boundary_i(faw_boundary_i),
       .crc_boundary_i(crc_boundary_i),
       .tdata_i       (tdata_i),
       .crc01_o       (crc01_calc),
       .crc23_o       (crc23_calc),
       .crc45_o       (crc45_calc),
       .crcvw_o       (crcvw_calc),
       .crc_valid_o   (crc_valid)
   );

   // CRC validation module
   qeciphy_crc_check i_crc_check (
       .clk_i         (clk_i),
       .rst_n_i       (rst_n_i),
       .crc_boundary_i(crc_boundary_i),
       .tdata_i       (tdata_i),
       .crc01_i       (crc01_calc),
       .crc23_i       (crc23_calc),
       .crc45_i       (crc45_calc),
       .crcvw_i       (crcvw_calc),
       .crc_valid_i   (crc_valid),
       .crc_error_o   (crc_check_error),
       .check_done_o  (crc_check_done)
   );

endmodule
