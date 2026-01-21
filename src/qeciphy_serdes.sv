// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// QECIPHY SERDES
//------------------------------------------------------------------------------
// This module implements a complete SERializer/DESerializer interface for the
// QECIPHY, handling all aspects of data conversion and alignment
// between the 64 bit datapath and GT hardware interface.
//
// Key Functions:
// 1. TX Serialization: Converts 64-bit protocol data to 32-bit GT data  
// 2. RX Deserialization: Converts 32-bit GT data to aligned 64-bit data
// 3. RX Byte Alignment: Automatically aligns byte boundaries using comma detection
// 4. RX Word Alignment: Automatically aligns word boundaries using FAW detection
// 5. GT Interface: Abstracts Xilinx GT primitive complexity from protocol logic
//
// Data Flow:
// TX: 64-bit@1x -> [tx_64b_to_32b] -> 32-bit@2x -> [GT wrapper] -> Physical Link
// RX: Physical Link -> [GT wrapper] -> 32-bit@2x -> [rx_bytealigner] -> 32-bit@2x -> [rx_32b_to_64b] -> 64-bit@1x 
//------------------------------------------------------------------------------

module qeciphy_serdes #(
    parameter GT_TYPE = "GTY"  // GT primitive type: "GTX", "GTY", or "GTH"
) (
    input  logic gt_ref_clk_i,    // GT reference clock input
    input  logic f_clk_i,         // Free-running fabric clock
    input  logic gt_rst_n_i,      // GT reset (active-low)
    output logic gt_power_good_o, // GT power good status

    // TX Interface
    output logic        tx_clk_o,             // TX clock output (GT generated)
    input  logic        tx_datapath_rst_n_i,  // TX datapath reset (active-low)
    input  logic [63:0] tx_tdata_i,           // 64-bit TX data
    output logic        gt_tx_rst_done_o,     // GT TX reset completion status

    // RX Interface
    output logic        rx_clk_o,              // RX clock output (GT generated)
    input  logic        rx_datapath_rst_n_i,   // RX datapath reset (active-low)
    output logic [63:0] rx_tdata_o,            // 64-bit RX data
    output logic        gt_rx_rst_done_o,      // GT RX reset completion status
    output logic        rx_datapath_aligned_o, // RX datapath alignment completion

    // GT differential signals
    input  logic        gt_rx_p,             // GT RX differential positive
    input  logic        gt_rx_n,             // GT RX differential negative
    output logic        gt_tx_p,             // GT TX differential positive
    output logic        gt_tx_n              // GT TX differential negative
);

   // RX Path Signals
   logic        rx_clk_2x;  // 2x RX clock from GT
   logic [31:0] rx_tdata_32b;  // 32-bit RX data from GT
   logic        rx_slide_rdy;  // GT slide ready signal
   logic        rx_slide;  // Slide request to GT for byte alignment
   logic        rx_byte_aligned;  // Byte alignment completion status
   logic        rx_word_aligned;  // Word alignment completion status

   // TX Path Signals  
   logic [31:0] tx_tdata_32b;  // 32-bit TX data to GT
   logic        tx_clk_2x;  // 2x TX clock from GT

   // Output Assignments
   assign rx_datapath_aligned_o = rx_word_aligned;

   // =========================================================================
   // TX Data Path: 64-bit to 32-bit Serialization
   // =========================================================================

   qeciphy_tx_64b_to_32b i_tx_64b_to_32b (
       .clk_i      (tx_clk_2x),            // 2x TX clock for 32-bit data serialization
       .rst_n_i    (tx_datapath_rst_n_i),  // TX datapath reset
       .tdata_64b_i(tx_tdata_i),           // 64-bit input
       .tdata_32b_o(tx_tdata_32b)          // 32-bit output to GT
   );

   // =========================================================================
   // RX Data Path Stage 1: Byte Alignment
   // =========================================================================

   qeciphy_rx_bytealigner #(
       .RX_DATA_WIDTH    (32),  // 32-bit data width from GT
       .TX_PATTERN_LENGTH(128)  // COMMA character comes every 128 words
   ) i_rx_bytealigner (
       .clk_i       (rx_clk_2x),            // 2x RX clock for 32-bit data processing
       .rst_n_i     (rx_datapath_rst_n_i),  // RX datapath reset
       .slide_rdy_i (rx_slide_rdy),         // GT slide ready signal
       .tdata_i     (rx_tdata_32b),         // 32-bit data from GT for comma detection
       .slide_o     (rx_slide),             // Slide request to GT
       .align_done_o(rx_byte_aligned),      // Byte alignment completion flag
       .align_fail_o()
   );

   // =========================================================================
   // RX Data Path Stage 2: Word Alignment and 32-bit to 64-bit Deserialization
   // =========================================================================

   qeciphy_rx_32b_to_64b i_rx_32b_to_64b (
       .clk_2x_i   (rx_clk_2x),        // 2x clock for 32-bit data capture
       .clk_i      (rx_clk_o),         // 1x clock for 64-bit data output
       .rst_n_i    (rx_byte_aligned),  // Reset released only after byte alignment
       .tdata_32b_i(rx_tdata_32b),     // 32-bit byte-aligned data from GT
       .tdata_64b_o(rx_tdata_o),       // 64-bit word-aligned data
       .aligned_o  (rx_word_aligned)   // Word alignment completion flag
   );

   // =========================================================================
   // GT Primitive Wrapper: Physical Layer Interface
   // =========================================================================

   (* KEEP_HIERARCHY = "TRUE" *)
   // Preserve hierarchy for constraints
   qeciphy_gt_wrapper #(
       .GT_TYPE(GT_TYPE)  // GT primitive type selection
   ) i_qeciphy_gt_wrapper (
       .gt_ref_clk_i   (gt_ref_clk_i),    // GT reference clock input
       .f_clk_i        (f_clk_i),         // Free-running clock input
       .gt_rst_n_i     (gt_rst_n_i),      // GT reset input
       .gt_power_good_o(gt_power_good_o), // GT power status output

       // TX Interface
       .tx_clk_o        (tx_clk_o),         // TX 1x clock output
       .tx_clk_2x_o     (tx_clk_2x),        // TX 2x clock output
       .tx_tdata_i      (tx_tdata_32b),     // 32-bit TX data input
       .gt_tx_rst_done_o(gt_tx_rst_done_o), // TX reset completion

       // RX Interface  
       .rx_clk_o        (rx_clk_o),          // RX 1x clock output
       .rx_clk_2x_o     (rx_clk_2x),         // RX 2x clock output
       .rx_tdata_o      (rx_tdata_32b),      // 32-bit RX data output
       .gt_rx_rst_done_o(gt_rx_rst_done_o),  // RX reset completion
       .rx_slide_rdy_o  (rx_slide_rdy),      // Slide ready status
       .rx_slide_i      (rx_slide),          // Slide request input

       // GT differential signals
       .gt_rx_p       (gt_rx_p),         // GT RX differential positive
       .gt_rx_n       (gt_rx_n),         // GT RX differential negative
       .gt_tx_p       (gt_tx_p),         // GT TX differential positive
       .gt_tx_n       (gt_tx_n)          // GT TX differential negative
   );

endmodule
