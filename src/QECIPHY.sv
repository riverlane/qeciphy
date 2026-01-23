// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// QECIPHY Top-Level Module
//------------------------------------------------------------------------------
// This module implements a complete high-speed serial communication protocol
// with automatic link establishment, error handling, and AXI4-Stream interfaces.
//
// Key Features:
// - Multi-gigabit serial communication using Xilinx GT transceivers
// - Automatic link training and alignment
// - CRC-based error detection
// - AXI4-Stream compliant user interfaces
// - Multi-clock domain design with proper CDC
// - Comprehensive error handling and status reporting
//
// Clock Domains:
// - ACLK:  AXI4-Stream interface clock (user application domain)
// - RCLK:  GT reference clock for transceiver operation
// - FCLK:  Free-running clock for fabric logic and reset control
// - TX/RX: GT-generated clocks
//
// Reset Strategy:
// - Hierarchical reset with proper sequencing across clock domains
//------------------------------------------------------------------------------

module QECIPHY #(
    parameter GT_TYPE = "GTY"  // GT transceiver type: "GTX", "GTY", or "GTH"
) (
    // =========================================================================
    // Clock and Reset Interface
    // =========================================================================
    input logic RCLK,  // GT reference clock
    input logic FCLK,  // Free-running fabric clock
    input logic ACLK,  // AXI4-Stream interface clock
    input logic ARSTn, // Master reset (active-low) synchronous to ACLK

    // =========================================================================
    // AXI4-Stream TX Interface (User -> QECIPHY)
    // =========================================================================
    input  logic [63:0] TX_TDATA,   // TX data input
    input  logic        TX_TVALID,  // TX data valid
    output logic        TX_TREADY,  // TX ready (backpressure)

    // =========================================================================
    // AXI4-Stream RX Interface (QECIPHY -> User)  
    // =========================================================================
    output logic [63:0] RX_TDATA,   // RX data output
    output logic        RX_TVALID,  // RX data valid
    input  logic        RX_TREADY,  // RX ready (backpressure)

    // =========================================================================
    // Status and Control Interface
    // =========================================================================
    output logic [3:0] STATUS,      // Link status code
    output logic [3:0] ECODE,       // Error code
    output logic       LINK_READY,  // Link ready for user data transfer
    output logic       FAULT_FATAL, // Fatal error detected

    // =========================================================================
    // GT Differential Signals
    // =========================================================================
    input  logic GT_RX_P,  // GT RX differential positive
    input  logic GT_RX_N,  // GT RX differential negative
    output logic GT_TX_P,  // GT TX differential positive
    output logic GT_TX_N   // GT TX differential negative
);

   // =========================================================================
   // Internal Signal Declarations
   // =========================================================================

   logic        reset_done;  // Reset sequence complete
   logic        fault_fatal;  // Internal fault aggregation
   logic [ 3:0] rx_error_code;  // RX error code
   logic        tx_fifo_overflow;  // TX FIFO overflow flag
   logic        tx_fifo_full;  // TX FIFO full flag
   logic        tx_fifo_ren;  // TX FIFO read enable
   logic        tx_fifo_wen;  // TX FIFO write enable
   logic [63:0] tx_fifo_rdata;  // TX FIFO read data
   logic        tx_fifo_empty;  // TX FIFO empty flag
   logic        axis_datapath_rst_n;  // AXI datapath reset
   logic        tx_datapath_rst_n;  // TX datapath reset
   logic        rx_datapath_rst_n;  // RX datapath reset
   logic        f_rst_n;  // ARSTn synchronized to FCLK
   logic        tx_rst_n;  // ARSTn synchronized to TX clock
   logic        rx_rst_n;  // ARSTn synchronized to RX clock
   logic        gt_rst_n;  // GT reset
   logic        tx_clk;  // TX clock
   logic        tx_ch_enc_tready;  // TX channel encoder AXIS tready
   logic [63:0] gt_tx_tdata;  // TX data from channel encoder
   logic        rx_clk;  // RX clock
   logic        rx_fifo_ren;  // RX FIFO read enable
   logic        rx_fifo_empty;  // RX FIFO empty flag
   logic        rx_ch_dec_tvalid;  // RX channel decoder AXIS tvalid
   logic [63:0] rx_ch_dec_tdata;  // RX data from channel decoder
   logic [63:0] gt_rx_tdata;  // RX data to channel decoder

   // CDC signals
   // Naming convention: <signal_name>_<clk_domain>
   // Legal clk_domain suffixes: 
   // 1. fclk -> FCLK domain
   // 2. tclk -> TX clock domain
   // 3. rclk -> RX clock domain
   // 4. aclk -> AXI clock domain

   logic        gt_power_good_fclk;
   logic        gt_power_good_aclk;

   logic        gt_tx_rst_done_tclk;
   logic        gt_tx_reset_done_aclk;

   logic        gt_rx_rst_done_rclk;
   logic        gt_rx_reset_done_aclk;

   logic        rx_datapath_aligned_rclk;
   logic        rx_datapath_aligned_aclk;

   logic        rx_fifo_overflow_rclk;
   logic        rx_fifo_overflow_aclk;

   logic        tx_link_enable_aclk;
   logic        tx_link_enable_tclk;

   logic        tx_data_enable_aclk;
   logic        tx_data_enable_tclk;

   logic        rx_rdy_rclk;
   logic        rx_rdy_tclk;
   logic        rx_rdy_aclk;

   logic        remote_rx_rdy_rclk;
   logic        remote_rx_rdy_aclk;

   logic        rx_fault_fatal_rclk;
   logic        rx_fault_fatal_aclk;

   logic        rx_enable_aclk;
   logic        rx_enable_rclk;

   // =========================================================================
   // Link State Machine Controller
   // =========================================================================

   qeciphy_controller i_qeciphy_controller (
       .clk_i                (ACLK),                      // AXI clock
       .rst_n_i              (ARSTn),                     // Master reset
       .reset_done_i         (reset_done),                // Reset sequence complete from qeciphy_resetcontroller
       .rx_ready_i           (rx_rdy_aclk),               // Local RX ready from qeciphy_rx_channeldecoder
       .remote_rx_ready_i    (remote_rx_rdy_aclk),        // Remote RX ready from qeciphy_rx_channeldecoder
       .rx_datapath_aligned_i(rx_datapath_aligned_aclk),  // Datapath alignment done from qeciphy_serdes
       .fault_fatal_i        (fault_fatal),               // Fatal fault input from qeciphy_error_handler
       .link_ready_o         (LINK_READY),                // Link operational
       .fault_fatal_o        (FAULT_FATAL),               // Fatal fault output
       .status_o             (STATUS),                    // Link status
       .tx_link_enable_o     (tx_link_enable_aclk),       // TX link enable to qeciphy_tx_channelencoder
       .tx_data_enable_o     (tx_data_enable_aclk),       // TX data enable to qeciphy_tx_channelencoder
       .rx_enable_o          (rx_enable_aclk)             // RX enable to qeciphy_rx_channeldecoder
   );

   // =========================================================================
   // Centralized Error Handler
   // =========================================================================

   qeciphy_error_handler i_qeciphy_error_handler (
       .clk_i             (ACLK),                   // AXI clock
       .rst_n_i           (ARSTn),                  // Master reset
       .rx_fault_fatal_i  (rx_fault_fatal_aclk),    // RX fault fatal from qeciphy_rx_channeldecoder
       .rx_error_code_i   (rx_error_code),          // RX error code from qeciphy_rx_channeldecoder
       .tx_fifo_overflow_i(tx_fifo_overflow),       // TX FIFO overflow
       .rx_fifo_overflow_i(rx_fifo_overflow_aclk),  // RX FIFO overflow
       .fault_fatal_o     (fault_fatal),            // Aggregated fault to qeciphy_controller
       .ecode_o           (ECODE)                   // Error code output
   );

   // =========================================================================
   // TX Data Path: AXI4-Stream -> Async FIFO -> Channel Encoder -> SERDES
   // =========================================================================

   // TX Interface Control Logic
   assign TX_TREADY   = ~tx_fifo_full && tx_data_enable_aclk;  // Ready when FIFO space available and data enabled
   assign tx_fifo_ren = ~tx_fifo_empty && tx_ch_enc_tready;  // Read when data available and encoder ready
   assign tx_fifo_wen = TX_TVALID && TX_TREADY;  // Write when user provides valid data and ready

   // TX Asynchronous FIFO: AXI Clock Domain -> TX Clock Domain  
   riv_async_fifo #(
       .DATA_WIDTH(64),
       .ADDR_WIDTH(6)
   ) i_tx_async_FIFO (
       // Write Interface (AXI Clock Domain)
       .wclk     (ACLK),                 // AXI clock
       .wrst_n   (axis_datapath_rst_n),  // AXI datapath reset overlapping with tx_datapath_rst_n
       .wen      (tx_fifo_wen),          // Write enable
       .wdata    (TX_TDATA),             // Write data
       .full     (tx_fifo_full),         // FIFO full flag
       .overflow (tx_fifo_overflow),     // Overflow flag
       .wwcount  (),
       // Read Interface (TX Clock Domain)
       .rclk     (tx_clk),               // TX clock
       .rrst_n   (tx_datapath_rst_n),    // TX datapath reset overlapping with axis_datapath_rst_n
       .ren      (tx_fifo_ren),          // Read enable
       .rdata    (tx_fifo_rdata),        // Read data
       .empty    (tx_fifo_empty),        // FIFO empty flag
       .underflow(),
       .rwcount  ()
   );

   // TX Channel Encoder: FIFO Data -> Encoded SERDES Data (+ FAW + CRC + IDLE Words)
   qeciphy_tx_channelencoder i_qeciphy_tx_channelencoder (
       .clk_i          (tx_clk),               // TX clock
       .rst_n_i        (tx_datapath_rst_n),    // TX datapath reset
       .s_axis_tdata_i (tx_fifo_rdata),        // Data from TX FIFO
       .s_axis_tvalid_i(~tx_fifo_empty),       // Valid when TX FIFO not empty
       .s_axis_tready_o(tx_ch_enc_tready),     // Ready to accept data
       .m_axis_tdata_o (gt_tx_tdata),          // Encoded data to qeciphy_serdes
       .link_enable_i  (tx_link_enable_tclk),  // Link enable from qeciphy_controller
       .data_enable_i  (tx_data_enable_tclk),  // User data enable from qeciphy_controller
       .rx_rdy_i       (rx_rdy_tclk)           // RX ready status from qeciphy_rx_channeldecoder
   );

   // =========================================================================
   // RX Data Path: SERDES -> Channel Decoder -> Async FIFO -> AXI4-Stream
   // =========================================================================

   // RX Interface Control Logic
   assign rx_fifo_ren = ~rx_fifo_empty && RX_TREADY;  // Read when data available and user ready
   assign RX_TVALID   = ~rx_fifo_empty && LINK_READY;  // Valid when data available and link ready

   // RX Asynchronous FIFO: RX Clock Domain -> AXI Clock Domain
   riv_async_fifo #(
       .DATA_WIDTH(64),
       .ADDR_WIDTH(6)
   ) i_rx_async_FIFO (
       // Write Interface (RX Clock Domain)
       .wclk     (rx_clk),                 // RX clock
       .wrst_n   (rx_datapath_rst_n),      // RX datapath reset overlapping with axis_datapath_rst_n
       .wen      (rx_ch_dec_tvalid),       // Write enable from rx_channeldecoder
       .wdata    (rx_ch_dec_tdata),        // Write data from rx_channeldecoder
       .full     (),
       .overflow (rx_fifo_overflow_rclk),  // Overflow flag
       .wwcount  (),
       // Read Interface (AXI Clock Domain)
       .rclk     (ACLK),                   // AXI clock
       .rrst_n   (axis_datapath_rst_n),    // AXI datapath reset overlapping with rx_datapath_rst_n
       .ren      (rx_fifo_ren),            // Read enable
       .rdata    (RX_TDATA),               // Data to user interface
       .empty    (rx_fifo_empty),          // FIFO empty flag
       .underflow(),
       .rwcount  ()
   );

   // RX Channel Decoder: SERDES Data -> Decoded User Data (- FAW - CRC - IDLE Words)
   // Also detects FAW, CRC errors
   qeciphy_rx_channeldecoder i_qeciphy_rx_channeldecoder (
       .clk_i           (rx_clk),               // RX clock
       .rst_n_i         (rx_datapath_rst_n),    // RX datapath reset
       .tdata_i         (gt_rx_tdata),          // Data from SERDES
       .tdata_o         (rx_ch_dec_tdata),      // Decoded user data
       .tvalid_o        (rx_ch_dec_tvalid),     // Data valid
       .enable_i        (rx_enable_rclk),       // RX enable from qeciphy_controller
       .rx_fault_fatal_o(rx_fault_fatal_rclk),  // Fatal RX error to qeciphy_error_handler
       .rx_error_code_o (rx_error_code),        // Error code to qeciphy_error_handler
       .rx_rdy_o        (rx_rdy_rclk),          // Local RX ready status to qeciphy_controller, qeciphy_tx_channelencoder
       .remote_rx_rdy_o (remote_rx_rdy_rclk)    // Remote RX ready status to qeciphy_controller
   );

   // =========================================================================
   // SERDES
   // =========================================================================

   qeciphy_serdes #(
       .GT_TYPE(GT_TYPE)  // GT primitive type selection
   ) i_qeciphy_serdes (
       // GT Reference and Control
       .gt_ref_clk_i   (RCLK),               // GT reference clock
       .f_clk_i        (FCLK),               // Free running fabric clock
       .gt_rst_n_i     (gt_rst_n),           // GT reset input from qeciphy_resetcontroller
       .gt_power_good_o(gt_power_good_fclk), // GT power status to qeciphy_resetcontroller

       // TX Interface
       .tx_clk_o           (tx_clk),              // TX clock output
       .tx_datapath_rst_n_i(tx_datapath_rst_n),   // TX datapath reset input from qeciphy_resetcontroller
       .tx_tdata_i         (gt_tx_tdata),         // 64 bit TX data input from qeciphy_tx_channelencoder
       .gt_tx_rst_done_o   (gt_tx_rst_done_tclk), // TX reset completion to qeciphy_resetcontroller

       // RX Interface
       .rx_clk_o             (rx_clk),                   // RX clock output
       .rx_datapath_rst_n_i  (rx_datapath_rst_n),        // RX datapath reset input from qeciphy_resetcontroller
       .rx_tdata_o           (gt_rx_tdata),              // 64 bit RX data output to qeciphy_rx_channeldecoder
       .gt_rx_rst_done_o     (gt_rx_rst_done_rclk),      // RX reset completion to qeciphy_resetcontroller
       .rx_datapath_aligned_o(rx_datapath_aligned_rclk), // RX alignment completion to qeciphy_controller

       // GT differential signals
       .gt_rx_p_i(GT_RX_P),  // GT RX differential positive
       .gt_rx_n_i(GT_RX_N),  // GT RX differential negative
       .gt_tx_p_o(GT_TX_P),  // GT TX differential positive
       .gt_tx_n_o(GT_TX_N)   // GT TX differential negative
   );

   // =========================================================================
   // Clock Domain Crossing (CDC)
   // =========================================================================

   qeciphy_cdc i_qeciphy_cdc (
       // RX Clock Domain Interface
       .rx_clk_i                  (rx_clk),                    // RX clock
       .rx_rst_n_i                (rx_rst_n),                  // RX reset (ARSTn synchronized to RX clock)
       .gt_rx_rst_done_rclk_i     (gt_rx_rst_done_rclk),
       .rx_fault_fatal_rclk_i     (rx_fault_fatal_rclk),
       .rx_rdy_rclk_i             (rx_rdy_rclk),
       .remote_rx_rdy_rclk_i      (remote_rx_rdy_rclk),
       .rx_fifo_overflow_rclk_i   (rx_fifo_overflow_rclk),
       .rx_datapath_aligned_rclk_i(rx_datapath_aligned_rclk),
       .rx_enable_rclk_o          (rx_enable_rclk),

       // TX Clock Domain Interface
       .tx_clk_i             (tx_clk),               // TX clock
       .tx_rst_n_i           (tx_rst_n),             // TX reset (ARSTn synchronized to TX clock)
       .gt_tx_rst_done_tclk_i(gt_tx_rst_done_tclk),
       .rx_rdy_tclk_o        (rx_rdy_tclk),
       .tx_link_enable_tclk_o(tx_link_enable_tclk),
       .tx_data_enable_tclk_o(tx_data_enable_tclk),

       // Fabric Clock Domain Interface
       .f_clk_i             (FCLK),               // Fabric clock
       .f_rst_n_i           (f_rst_n),            // Fabric reset (ARSTn synchronized to FCLK)
       .gt_power_good_fclk_i(gt_power_good_fclk),

       // AXI Clock Domain Interface
       .axis_clk_i                (ACLK),                     // AXI clock
       .axis_rst_n_i              (ARSTn),                    // AXI reset
       .rx_enable_aclk_i          (rx_enable_aclk),
       .tx_link_enable_aclk_i     (tx_link_enable_aclk),
       .tx_data_enable_aclk_i     (tx_data_enable_aclk),
       .gt_rx_rst_done_aclk_o     (gt_rx_reset_done_aclk),
       .gt_tx_rst_done_aclk_o     (gt_tx_reset_done_aclk),
       .gt_power_good_aclk_o      (gt_power_good_aclk),
       .rx_fault_fatal_aclk_o     (rx_fault_fatal_aclk),
       .rx_rdy_aclk_o             (rx_rdy_aclk),
       .remote_rx_rdy_aclk_o      (remote_rx_rdy_aclk),
       .rx_fifo_overflow_aclk_o   (rx_fifo_overflow_aclk),
       .rx_datapath_aligned_aclk_o(rx_datapath_aligned_aclk)
   );

   // =========================================================================
   // Multi-Domain Reset Controller
   // =========================================================================

   qeciphy_resetcontroller i_qeciphy_resetcontroller (
       // Primary Control Interface (AXI Clock Domain)
       .axis_clk_i           (ACLK),                   // AXI clock
       .axis_rst_n_i         (ARSTn),                  // Master reset
       .gt_power_good_i      (gt_power_good_aclk),     // GT power good status from qeciphy_serdes
       .gt_tx_rst_done_i     (gt_tx_reset_done_aclk),  // GT TX reset completion from qeciphy_serdes
       .gt_rx_rst_done_i     (gt_rx_reset_done_aclk),  // GT RX reset completion from qeciphy_serdes
       .axis_datapath_rst_n_o(axis_datapath_rst_n),    // AXI datapath reset output
       .rst_done_o           (reset_done),             // Reset sequence completion output to qeciphy_controller

       // TX Clock Domain Reset Generation
       .tx_clk_i           (tx_clk),            // TX clock
       .tx_rst_n_o         (tx_rst_n),          // TX domain reset (ARSTn synchronized to TX clock)
       .tx_datapath_rst_n_o(tx_datapath_rst_n), // TX datapath reset

       // RX Clock Domain Reset Generation
       .rx_clk_i           (rx_clk),            // RX clock
       .rx_rst_n_o         (rx_rst_n),          // RX domain reset (ARSTn synchronized to RX clock)
       .rx_datapath_rst_n_o(rx_datapath_rst_n), // RX datapath reset

       // Fabric Clock Domain Reset Generation
       .f_clk_i   (FCLK),     // Fabric clock
       .f_rst_n_o (f_rst_n),  // Fabric domain reset (ARSTn synchronized to FCLK)
       .gt_rst_n_o(gt_rst_n)  // GT reset output
   );

endmodule  // QECIPHY
