// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta

// This module implements an asynchronous FIFO using LUTRAM.  
// The architecture itself does not impose constraints on the frequency range of WCLK and RCLK.
//
// Parameters:
//
// 1. DATA_WIDTH (int): Defines the data width of the FIFO. 
// 2. ADDR_WIDTH (int): Specifies the FIFO depth, where depth = 2**ADDR_WIDTH - 1.

`ifndef RIV_ASYNC_FIFO_SV
`define RIV_ASYNC_FIFO_SV

module riv_async_fifo #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 10
) (
    input  logic                  wclk,
    input  logic                  wrst_n,
    input  logic                  wen,
    input  logic [DATA_WIDTH-1:0] wdata,
    input  logic                  rclk,
    input  logic                  rrst_n,
    input  logic                  ren,
    output logic [DATA_WIDTH-1:0] rdata,
    output logic                  full,
    output logic                  empty,
    output logic                  overflow,
    output logic                  underflow,
    output logic [ADDR_WIDTH-1:0] wwcount,
    output logic [ADDR_WIDTH-1:0] rwcount
);

   // -------------------------------------------------------------
   // Declaration
   // -------------------------------------------------------------

   logic [ADDR_WIDTH-1:0] waddr;
   logic [ADDR_WIDTH-1:0] waddr_rd;

   logic [ADDR_WIDTH-1:0] raddr;
   logic [ADDR_WIDTH-1:0] raddr_wr;

   logic wr_fsm_load;
   logic wr_fsm_req_ack;
   logic wr_fsm_recv_ack;

   logic rd_fsm_load;
   logic rd_fsm_req_ack;
   logic rd_fsm_recv_ack;

   // -------------------------------------------------------------
   // Write Control
   // -------------------------------------------------------------

   riv_async_fifo_ctl #(
       .ADDR_WIDTH(ADDR_WIDTH)
   ) i_fifo_wctl (
       .clk         (wclk),
       .rst_n       (wrst_n),
       .en          (wen),
       .addr        (waddr),
       .fsm_load    (wr_fsm_load),
       .fsm_req_ack (wr_fsm_req_ack),
       .fsm_recv_ack(wr_fsm_recv_ack)
   );

   // -------------------------------------------------------------
   // Read Control
   // -------------------------------------------------------------

   riv_async_fifo_ctl #(
       .ADDR_WIDTH(ADDR_WIDTH)
   ) i_fifo_rctl (
       .clk         (rclk),
       .rst_n       (rrst_n),
       .en          (ren),
       .addr        (raddr),
       .fsm_load    (rd_fsm_load),
       .fsm_req_ack (rd_fsm_req_ack),
       .fsm_recv_ack(rd_fsm_recv_ack)
   );

   // -------------------------------------------------------------
   // Memory
   // -------------------------------------------------------------

   riv_async_fifo_mem #(
       .ADDR_WIDTH(ADDR_WIDTH),
       .DATA_WIDTH(DATA_WIDTH)
   ) i_fifo_mem (
       .wclk (wclk),
       .wen  (wen),
       .waddr(waddr),
       .wdata(wdata),
       .raddr(raddr),
       .rdata(rdata)
   );

   // -------------------------------------------------------------
   // CDC
   // -------------------------------------------------------------

   riv_async_fifo_cdc #(
       .ADDR_WIDTH(ADDR_WIDTH)
   ) i_fifo_cdc (
       .wclk           (wclk),
       .wrst_n         (wrst_n),
       .wr_fsm_load    (wr_fsm_load),
       .wr_fsm_req_ack (wr_fsm_req_ack),
       .wr_fsm_recv_ack(wr_fsm_recv_ack),
       .waddr          (waddr),
       .raddr_wr       (raddr_wr),

       .rclk           (rclk),
       .rrst_n         (rrst_n),
       .rd_fsm_load    (rd_fsm_load),
       .rd_fsm_req_ack (rd_fsm_req_ack),
       .rd_fsm_recv_ack(rd_fsm_recv_ack),
       .raddr          (raddr),
       .waddr_rd       (waddr_rd)
   );

   // -------------------------------------------------------------
   // Word count in the FIFO
   // -------------------------------------------------------------

   // waddr and raddr are treated as unsigned signals.
   // Even for waddr < raddr, the result will be positive because of wrapping

   // Word count in RCLK domain
   always_ff @(posedge rclk) begin
      rwcount <= waddr_rd - raddr;
   end

   // Word count in WCLK domain
   always_ff @(posedge wclk) begin
      wwcount <= waddr - raddr_wr;
   end

   // -------------------------------------------------------------
   // Output signal generation
   // -------------------------------------------------------------

   assign full = (waddr == (raddr_wr - ADDR_WIDTH'(1'b1)));
   assign empty = (waddr_rd == raddr);
   assign overflow = wen && full;
   assign underflow = ren && empty;

endmodule  // riv_async_fifo

`endif  // RIV_ASYNC_FIFO_SV
