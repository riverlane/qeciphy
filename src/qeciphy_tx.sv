// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: aniketEng

module qeciphy_tx (
    input  logic        axis_clk,
    input  logic        axis_rst_n,
    input  logic [63:0] i_data,
    input  logic        i_valid,
    output logic        o_ready,
    input  logic        i_remote_rx_rdy_axis,
    input  logic        i_pd_req_axis,
    input  logic        i_pd_ack_axis,

    input logic tx_clk,
    input logic tx_rst_n,
    input logic i_rx_rdy,
    input logic i_remote_rx_rdy,
    input logic i_pd_req,
    input logic i_pd_ack,

    input  logic        gt_tx_clk,
    output logic [31:0] o_gt_tx_data
);

   // -------------------------------------------------------------
   // Local declaration
   // -------------------------------------------------------------

   logic fifo_full;
   logic fifo_empty;
   logic fifo_wen;
   logic fifo_ren;
   logic ch_enc_rdy;
   logic [63:0] fifo_rdata;

   // -------------------------------------------------------------
   // General
   // -------------------------------------------------------------

   assign o_ready  = ~fifo_full && i_remote_rx_rdy_axis && ~i_pd_req_axis && ~i_pd_ack_axis && axis_rst_n;
   assign fifo_wen = i_valid && o_ready;
   assign fifo_ren = ~fifo_empty && ch_enc_rdy;

   // -------------------------------------------------------------
   // Asynchronous FIFO instance
   // -------------------------------------------------------------

   riv_async_fifo #(
       .DATA_WIDTH(64),
       .ADDR_WIDTH(6)
   ) tx_async_FIFO (
       .wclk(axis_clk),
       .wrst_n(axis_rst_n),
       .wen(fifo_wen),
       .wdata(i_data),
       .full(fifo_full),
       .overflow(),
       .wwcount(),
       .rclk(tx_clk),
       .rrst_n(tx_rst_n),
       .ren(fifo_ren),
       .rdata(fifo_rdata),
       .empty(fifo_empty),
       .underflow(),
       .rwcount()
   );

   // -------------------------------------------------------------
   // Channel encoder instance
   // -------------------------------------------------------------

   qeciphy_tx_channelencoder i_qeciphy_tx_channelencoder (
       .gt_tx_clk      (gt_tx_clk),
       .o_gt_tx_data   (o_gt_tx_data),
       .tx_clk         (tx_clk),
       .rst_n          (tx_rst_n),
       .i_tx_data      (fifo_rdata),
       .o_tx_ready     (ch_enc_rdy),
       .i_tx_valid     (~fifo_empty),
       .i_rx_rdy       (i_rx_rdy),
       .i_remote_rx_rdy(i_remote_rx_rdy),
       .i_pd_req       (i_pd_req),
       .i_pd_ack       (i_pd_ack)
   );

endmodule  // qeciphy_tx
