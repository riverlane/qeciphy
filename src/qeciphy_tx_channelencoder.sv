// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// TX Channel Encoder
//------------------------------------------------------------------------------
// Top-level transmitter channel encoder that orchestrates boundary generation,
// transmission state control, and packet generation for the QECIPHY TX path.
//
// Architecture:
// - TX Boundary Generator: Generates FAW and CRC timing boundaries
// - TX Controller: Manages transmission states (off/idle/active)
// - TX Packet Generator: Creates FAWs, inserts CRC, handles user data
//
// Data Flow: s_axis_tdata_i -> qeciphy_tx_packet_gen -> m_axis_tdata_o
// Control Flow: {link_enable_i, data_enable_i} -> qeciphy_tx_controller -> tx_states -> qeciphy_tx_packet_gen
// Timing Flow: qeciphy_tx_boundary_gen -> boundaries -> {qeciphy_tx_controller, qeciphy_tx_packet_gen}
//------------------------------------------------------------------------------

module qeciphy_tx_channelencoder (
    input  logic        clk_i,                 // Clock input
    input  logic        rst_n_i,               // Active-low reset
    input  logic [63:0] s_axis_tdata_i,        // Input user data stream
    input  logic        s_axis_tvalid_i,       // Input data valid signal
    output logic        s_axis_tready_o,       // Ready to accept input data
    output logic [63:0] m_axis_tdata_o,        // Output data stream
    output logic        m_axis_tdata_isfaw_o,  // Output indicates if m_axis_tdata is FAW
    input  logic        link_enable_i,         // Link enable control
    input  logic        data_enable_i,         // Data transmission enable
    input  logic        rx_rdy_i               // Receiver ready status for FAW packets
);

   logic faw_boundary;  // FAW boundary timing signal from qeciphy_tx_boundary_gen
   logic almost_faw_boundary;  // Early FAW boundary warning from qeciphy_tx_boundary_gen  
   logic crc_boundary;  // CRC boundary timing signal from qeciphy_tx_boundary_gen
   logic tx_off;  // TX off state from qeciphy_tx_controller
   logic tx_idle;  // TX idle state from qeciphy_tx_controller
   logic tx_active;  // TX active state from qeciphy_tx_controller

   //--------------------------------------------------------------------------
   // TX Controller Instance
   //--------------------------------------------------------------------------
   qeciphy_tx_controller tx_controller_inst (
       .clk_i                (clk_i),                // Clock input
       .rst_n_i              (rst_n_i),              // Active-low reset
       .almost_faw_boundary_i(almost_faw_boundary),  // Frame boundary timing from qeciphy_tx_boundary_gen
       .link_enable_i        (link_enable_i),        // External link enable input
       .data_enable_i        (data_enable_i),        // External data enable input
       .tx_off_o             (tx_off),               // TX off state output
       .tx_idle_o            (tx_idle),              // TX idle state output
       .tx_active_o          (tx_active)             // TX active state output
   );

   //--------------------------------------------------------------------------
   // TX Boundary Generator Instance
   //--------------------------------------------------------------------------
   qeciphy_tx_boundary_gen tx_boundary_gen_inst (
       .clk_i                (clk_i),                // Clock input
       .rst_n_i              (rst_n_i),              // Active-low reset
       .almost_faw_boundary_o(almost_faw_boundary),  // Early FAW boundary warning output
       .faw_boundary_o       (faw_boundary),         // FAW boundary timing output
       .crc_boundary_o       (crc_boundary)          // CRC boundary timing output
   );

   //--------------------------------------------------------------------------
   // TX Packet Generator Instance
   //--------------------------------------------------------------------------
   qeciphy_tx_packet_gen tx_packet_gen_inst (
       .clk_i               (clk_i),                 // Clock input
       .rst_n_i             (rst_n_i),               // Active-low reset
       .faw_boundary_i      (faw_boundary),          // FAW boundary timing from qeciphy_tx_boundary_gen
       .crc_boundary_i      (crc_boundary),          // CRC boundary timing from qeciphy_tx_boundary_gen
       .s_axis_tdata_i      (s_axis_tdata_i),        // Input user data stream
       .s_axis_tvalid_i     (s_axis_tvalid_i),       // Input data valid signal
       .s_axis_tready_o     (s_axis_tready_o),       // Ready to accept input data output
       .m_axis_tdata_o      (m_axis_tdata_o),        // Output data stream
       .m_axis_tdata_isfaw_o(m_axis_tdata_isfaw_o),  // Output indicates if m_axis_tdata is FAW
       .tx_off_i            (tx_off),                // TX off state from qeciphy_tx_controller
       .tx_idle_i           (tx_idle),               // TX idle state from qeciphy_tx_controller
       .tx_active_i         (tx_active),             // TX active state from qeciphy_tx_controller
       .rx_rdy_i            (rx_rdy_i)               // Receiver ready status for FAW packets
   );

endmodule  // qeciphy_tx_channelencoder
