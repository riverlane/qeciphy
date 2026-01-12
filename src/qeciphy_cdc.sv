// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// Clock Domain Crossing (CDC) module
//------------------------------------------------------------------------------
// This module safely synchronizes control and status signals between multiple
// clock domains in the QECIPHY design:
// - rx_clk_i:   RX clock domain
// - tx_clk_i:   TX clock domain
// - f_clk_i:    Free running clock domain
// - axis_clk_i: AXI Stream clock domain
//
// All synchronizations use 2-FF synchronizers to prevent metastability
// when crossing asynchronous clock boundaries.
//
// Signal Flow:
// - Control signals flow from AXI Stream domain to RX/TX domains
// - Status signals flow from RX/TX/Free running domains to AXI Stream domain
//------------------------------------------------------------------------------

module qeciphy_cdc (
    // =========================================================================
    // RX Clock Domain Interface
    // =========================================================================
    input  logic rx_clk_i,                     // RX clock
    input  logic rx_rst_n_i,                   // RX domain active-low reset
    input  logic gt_rx_rst_done_rclk_i,        // GT RX reset completion
    input  logic rx_fault_fatal_rclk_i,        // RX fault status
    input  logic rx_rdy_rclk_i,                // Local RX ready status
    input  logic remote_rx_rdy_rclk_i,         // Remote RX ready status
    input  logic rx_fifo_overflow_rclk_i,      // RX FIFO overflow status
    input  logic rx_datapath_rst_done_rclk_i,  // RX datapath reset done
    output logic rx_enable_rclk_o,             // RX enable control

    // =========================================================================
    // TX Clock Domain Interface  
    // =========================================================================
    input  logic tx_clk_i,               // TX clock
    input  logic tx_rst_n_i,             // TX domain active-low reset
    input  logic gt_tx_rst_done_tclk_i,  // GT TX reset completion
    output logic rx_rdy_tclk_o,          // RX ready status
    output logic tx_link_enable_tclk_o,  // TX link enable control
    output logic tx_data_enable_tclk_o,  // TX data enable control

    // =========================================================================
    // Fabric/GT Clock Domain Interface
    // =========================================================================
    input logic f_clk_i,              // Free running clock
    input logic f_rst_n_i,            // Free running domain active-low reset
    input logic gt_power_good_fclk_i, // GT power good status

    // =========================================================================
    // AXI Stream Clock Domain Interface
    // =========================================================================
    input  logic axis_clk_i,                  // AXI Stream interface clock
    input  logic axis_rst_n_i,                // AXIS domain active-low reset
    input  logic rx_enable_aclk_i,            // RX enable command
    input  logic tx_link_enable_aclk_i,       // TX link enable command
    input  logic tx_data_enable_aclk_i,       // TX data enable command
    output logic gt_rx_rst_done_aclk_o,       // GT RX reset done status
    output logic gt_tx_rst_done_aclk_o,       // GT TX reset done status
    output logic gt_power_good_aclk_o,        // GT power good status
    output logic rx_fault_fatal_aclk_o,       // RX fault status
    output logic rx_rdy_aclk_o,               // RX ready status
    output logic remote_rx_rdy_aclk_o,        // Remote RX ready status
    output logic rx_fifo_overflow_aclk_o,     // RX FIFO overflow status
    output logic rx_datapath_rst_done_aclk_o  // RX datapath reset done status
);

   // =========================================================================
   // Clock Domain Crossing: AXIS Clock -> RX Clock Domain
   // =========================================================================

   riv_synchronizer_2ff i_cdc_rx_enable_rclk (
       .src_in(rx_enable_aclk_i),
       .dst_clk(rx_clk_i),
       .dst_rst_n(rx_rst_n_i),
       .dst_out(rx_enable_rclk_o)
   );

   // =========================================================================
   // Clock Domain Crossing: Multiple Sources -> TX Clock Domain
   // =========================================================================

   riv_synchronizer_2ff i_cdc_rx_rdy_tclk (
       .src_in(rx_rdy_rclk_i),
       .dst_clk(tx_clk_i),
       .dst_rst_n(tx_rst_n_i),
       .dst_out(rx_rdy_tclk_o)
   );

   riv_synchronizer_2ff i_cdc_tx_link_enable_tclk (
       .src_in(tx_link_enable_aclk_i),
       .dst_clk(tx_clk_i),
       .dst_rst_n(tx_rst_n_i),
       .dst_out(tx_link_enable_tclk_o)
   );

   riv_synchronizer_2ff i_cdc_tx_data_enable_tclk (
       .src_in(tx_data_enable_aclk_i),
       .dst_clk(tx_clk_i),
       .dst_rst_n(tx_rst_n_i),
       .dst_out(tx_data_enable_tclk_o)
   );

   // =========================================================================
   // Clock Domain Crossing: Multiple Sources -> AXIS Clock Domain
   // =========================================================================

   riv_synchronizer_2ff i_cdc_gt_rx_rst_done_aclk (
       .src_in(gt_rx_rst_done_rclk_i),
       .dst_clk(axis_clk_i),
       .dst_rst_n(axis_rst_n_i),
       .dst_out(gt_rx_rst_done_aclk_o)
   );

   riv_synchronizer_2ff i_cdc_gt_tx_rst_done_aclk (
       .src_in(gt_tx_rst_done_tclk_i),
       .dst_clk(axis_clk_i),
       .dst_rst_n(axis_rst_n_i),
       .dst_out(gt_tx_rst_done_aclk_o)
   );

   riv_synchronizer_2ff i_cdc_gt_power_good_aclk (
       .src_in(gt_power_good_fclk_i),
       .dst_clk(axis_clk_i),
       .dst_rst_n(axis_rst_n_i),
       .dst_out(gt_power_good_aclk_o)
   );

   riv_synchronizer_2ff i_cdc_rx_fault_fatal_aclk (
       .src_in(rx_fault_fatal_rclk_i),
       .dst_clk(axis_clk_i),
       .dst_rst_n(axis_rst_n_i),
       .dst_out(rx_fault_fatal_aclk_o)
   );

   riv_synchronizer_2ff i_cdc_rx_rdy_aclk (
       .src_in(rx_rdy_rclk_i),
       .dst_clk(axis_clk_i),
       .dst_rst_n(axis_rst_n_i),
       .dst_out(rx_rdy_aclk_o)
   );

   riv_synchronizer_2ff i_cdc_remote_rx_rdy_aclk (
       .src_in(remote_rx_rdy_rclk_i),
       .dst_clk(axis_clk_i),
       .dst_rst_n(axis_rst_n_i),
       .dst_out(remote_rx_rdy_aclk_o)
   );

   riv_synchronizer_2ff i_cdc_rx_fifo_overflow_aclk (
       .src_in(rx_fifo_overflow_rclk_i),
       .dst_clk(axis_clk_i),
       .dst_rst_n(axis_rst_n_i),
       .dst_out(rx_fifo_overflow_aclk_o)
   );

   riv_synchronizer_2ff i_cdc_rx_datapath_rst_done_aclk (
       .src_in(rx_datapath_rst_done_rclk_i),
       .dst_clk(axis_clk_i),
       .dst_rst_n(axis_rst_n_i),
       .dst_out(rx_datapath_rst_done_aclk_o)
   );

endmodule
