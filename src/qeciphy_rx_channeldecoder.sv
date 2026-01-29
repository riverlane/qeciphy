// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// RX Channel Decoder
//------------------------------------------------------------------------------
// Top-level receiver channel decoder that orchestrates frame boundary detection,
// data processing, and error management for the QECIPHY.
//
// Architecture:
// - RX Controller: Manages enable signals and error handling
// - Boundary Generator: Detects / generates boundaries
// - Monitor: Processes aligned data, validates CRC/FAW, and outputs decoded data
//
// Data Flow: tdata_i -> qeciphy_rx_boundary_gen -> qeciphy_rx_monitor -> tdata_o
// Control Flow: enable_i -> qeciphy_rx_controller -> rx_enable -> {qeciphy_rx_boundary_gen, qeciphy_rx_monitor}
// Error Flow: {monitor errors} -> qeciphy_rx_controller -> rx_fault_fatal_o
//------------------------------------------------------------------------------

module qeciphy_rx_channeldecoder (
    input  logic        clk_i,             // Clock input
    input  logic        rst_n_i,           // Active-low reset    
    input  logic [63:0] tdata_i,           // Input data stream
    output logic [63:0] tdata_o,           // Output data stream
    output logic        tvalid_o,          // Output data valid signal
    input  logic        enable_i,          // Channel decoder enable
    output logic        rx_fault_fatal_o,  // Fatal RX fault detected
    output logic [ 3:0] rx_error_code_o,   // RX error code output
    output logic        rx_rdy_o,          // Local RX ready status
    output logic        remote_rx_rdy_o    // Remote RX ready status
);

   logic        rx_locked;  // Frame lock status from qeciphy_rx_boundary_gen
   logic        rx_enable;  // Internal enable signal from qeciphy_rx_controller
   logic        crc_boundary;  // CRC frame boundary indicator
   logic        faw_boundary;  // FAW (Frame Alignment Word) boundary indicator
   logic        faw_error;  // FAW validation error
   logic        crc_error;  // CRC validation error
   logic [63:0] tdata_aligned;  // Frame-aligned data from qeciphy_rx_boundary_gen to qeciphy_rx_monitor

   //--------------------------------------------------------------------------
   // RX Controller Instance
   //--------------------------------------------------------------------------
   qeciphy_rx_controller i_rx_controller (
       .clk_i           (clk_i),             // Clock input
       .rst_n_i         (rst_n_i),           // Active-low reset
       .enable_i        (enable_i),          // External enable input
       .rx_locked_i     (rx_locked),         // Frame lock status from qeciphy_rx_boundary_gen
       .crc_err_i       (crc_error),         // CRC error from qeciphy_rx_monitor
       .faw_err_i       (faw_error),         // FAW error from qeciphy_rx_monitor
       .rx_enable_o     (rx_enable),         // RX subsystem enable
       .rx_rdy_o        (rx_rdy_o),          // RX ready status output
       .rx_fault_fatal_o(rx_fault_fatal_o),  // Fatal fault indicator output
       .rx_error_code_o (rx_error_code_o)    // RX error code output
   );

   //--------------------------------------------------------------------------
   // RX Boundary Generator Instance  
   //--------------------------------------------------------------------------
   qeciphy_rx_boundary_gen i_qeciphy_rx_boundary_gen (
       .clk_i         (clk_i),          // Clock input
       .rst_n_i       (rst_n_i),        // Active-low reset
       .tdata_i       (tdata_i),        // Input data stream
       .tdata_o       (tdata_aligned),  // Output frame-aligned data stream (pass-through)
       .enable_i      (rx_enable),      // Enable from qeciphy_rx_controller
       .locked_o      (rx_locked),      // Frame lock status output
       .faw_boundary_o(faw_boundary),   // FAW boundary indicator
       .crc_boundary_o(crc_boundary)    // CRC boundary indicator
   );

   //--------------------------------------------------------------------------
   // RX Monitor Instance
   //--------------------------------------------------------------------------
   qeciphy_rx_monitor i_rx_monitor (
       .clk_i          (clk_i),           // Clock input
       .rst_n_i        (rst_n_i),         // Active-low reset
       .tdata_i        (tdata_aligned),   // Frame-aligned input data
       .tdata_o        (tdata_o),         // Output data (11 cycles latency)
       .tvalid_o       (tvalid_o),        // Output data valid signal (FAW, CRC, Idle words removed)
       .enable_i       (rx_enable),       // Enable from controller
       .faw_boundary_i (faw_boundary),    // FAW boundary from boundary generator
       .crc_boundary_i (crc_boundary),    // CRC boundary from boundary generator
       .crc_error_o    (crc_error),       // CRC validation error
       .faw_error_o    (faw_error),       // FAW validation error
       .remote_rx_rdy_o(remote_rx_rdy_o)  // Remote RX ready status
   );

endmodule
