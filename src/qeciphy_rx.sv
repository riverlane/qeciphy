// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_rx (
    input  logic        axis_clk,
    input  logic        axis_rst_n,
    output logic [63:0] o_data,
    output logic        o_valid,
    input  logic        i_ready,
    input  logic        gt_rx_clk,
    input  logic [31:0] i_gt_rx_data,
    input  logic        i_rx_slide_rdy,
    output logic        o_rx_slide,
    input  logic        rx_clk,
    input  logic        rx_rst_n,
    output logic        o_rx_rdy,
    output logic        o_remote_rx_rdy,
    output logic        o_remote_pd_req,
    output logic        o_remote_pd_ack,
    output logic        o_fap_missing,
    output logic        o_crc_mismatch
);

   // -------------------------------------------------------------
   // Local declaration
   // -------------------------------------------------------------

   logic fifo_full;
   logic fifo_wen;
   logic fifo_ren;
   logic fifo_empty;
   logic ch_dec_o_valid;
   logic [63:0] fifo_wdata;

   logic byte_align_done;

   logic remote_pd_req;
   logic remote_pd_ack;

   // -------------------------------------------------------------
   // General
   // -------------------------------------------------------------

   assign fifo_wen = ~fifo_full && ch_dec_o_valid;
   assign fifo_ren = ~fifo_empty && i_ready;
   assign o_valid = ~fifo_empty && axis_rst_n;

   assign o_remote_pd_req = fifo_empty && remote_pd_req;
   assign o_remote_pd_ack = fifo_empty && remote_pd_ack;

   // -------------------------------------------------------------
   // Byte aligner instance
   // -------------------------------------------------------------

   qeciphy_rx_bytealigner #(
       .RX_DATA_WIDTH    (32),
       .TX_PATTERN_LENGTH(1024)
   ) i_qeciphy_rx_bytealigner (
       .clk           (gt_rx_clk),
       .rst_n         (rx_rst_n),
       .i_rx_slide_rdy(i_rx_slide_rdy),
       .i_rx_data     (i_gt_rx_data),
       .o_rx_slide    (o_rx_slide),
       .o_align_done  (byte_align_done),
       .o_align_fail  ()
   );

   // -------------------------------------------------------------
   // Channel decoder instance
   // -------------------------------------------------------------

   qeciphy_rx_channeldecoder i_qeciphy_rx_channeldecoder (
       .gt_rx_clk(gt_rx_clk),
       .rx_clk(rx_clk),
       .rst_n(byte_align_done),
       .i_gt_rx_data(i_gt_rx_data),
       .o_rx_data(fifo_wdata),
       .o_rx_valid(ch_dec_o_valid),
       .o_rx_rdy(o_rx_rdy),
       .o_remote_rx_rdy(o_remote_rx_rdy),
       .o_remote_pd_req(remote_pd_req),
       .o_remote_pd_ack(remote_pd_ack),
       .o_fap_missing(o_fap_missing),
       .o_crc_mismatch(o_crc_mismatch)
   );

   // -------------------------------------------------------------
   // Asynchronous FIFO instance
   // -------------------------------------------------------------

   riv_async_fifo #(
       .DATA_WIDTH(64),
       .ADDR_WIDTH(6)
   ) rx_async_FIFO (
       .wclk(rx_clk),
       .wrst_n(rx_rst_n),
       .wen(fifo_wen),
       .wdata(fifo_wdata),
       .full(fifo_full),
       .overflow(),
       .wwcount(),
       .rclk(axis_clk),
       .rrst_n(axis_rst_n),
       .ren(fifo_ren),
       .rdata(o_data),
       .empty(fifo_empty),
       .underflow(),
       .rwcount()
   );

endmodule  // qeciphy_rx
