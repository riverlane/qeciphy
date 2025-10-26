// SPDX-License-Identifier: None
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

`ifndef RIV_ASYNC_FIFO_CDC_SV
`define RIV_ASYNC_FIFO_CDC_SV

module riv_async_fifo_cdc #(
    parameter ADDR_WIDTH = 10
) (
    input  logic                  wclk,
    input  logic                  wrst_n,
    input  logic                  wr_fsm_load,
    input  logic                  wr_fsm_req_ack,
    output logic                  wr_fsm_recv_ack,
    input  logic [ADDR_WIDTH-1:0] waddr,
    output logic [ADDR_WIDTH-1:0] raddr_wr,

    input  logic                  rclk,
    input  logic                  rrst_n,
    input  logic                  rd_fsm_load,
    input  logic                  rd_fsm_req_ack,
    output logic                  rd_fsm_recv_ack,
    input  logic [ADDR_WIDTH-1:0] raddr,
    output logic [ADDR_WIDTH-1:0] waddr_rd
);

   // -------------------------------------------------------------
   // Declaration
   // -------------------------------------------------------------

   logic [ADDR_WIDTH-1:0] waddr_rd_nxt;
   logic [ADDR_WIDTH-1:0] waddr_latch;
   logic [ADDR_WIDTH-1:0] waddr_latch_nxt;

   logic wr_fsm_req_ack_rd;
   logic waddr_sample_rd;
   logic wr_fsm_recv_ack_rd;

   logic [ADDR_WIDTH-1:0] raddr_wr_nxt;
   logic [ADDR_WIDTH-1:0] raddr_latch;
   logic [ADDR_WIDTH-1:0] raddr_latch_nxt;

   logic rd_fsm_req_ack_wr;
   logic raddr_sample_wr;
   logic rd_fsm_recv_ack_wr;

   // -------------------------------------------------------------
   // Taking WADDR from WCLK domain to RCLK domain
   // -------------------------------------------------------------

   // WADDR is latched into a stable register during the LOAD state for transfer to the RCLK domain.
   assign waddr_latch_nxt = wr_fsm_load ? waddr : waddr_latch;

   always_ff @(posedge wclk or negedge wrst_n) begin
      if (~wrst_n) begin
         waddr_latch <= '0;
      end else begin
         waddr_latch <= waddr_latch_nxt;
      end
   end

   // Request the RCLK domain to sample WADDR when in REQ_ACK state.
   riv_synchronizer_2ff i_waddr_load_cdc (
       .src_in(wr_fsm_req_ack),
       .dst_clk(rclk),
       .dst_rst_n(rrst_n),
       .dst_out(wr_fsm_req_ack_rd)
   );

   // Generate an acknowledge signal in the RCLK domain to indicate that WADDR has been successfully sampled.
   always_ff @(posedge rclk or negedge rrst_n) begin
      if (~rrst_n) begin
         wr_fsm_recv_ack_rd <= 1'b0;
      end else begin
         wr_fsm_recv_ack_rd <= wr_fsm_req_ack_rd;
      end
   end

   // Detect positive edge of wr_fsm_req_ack_rd
   assign waddr_sample_rd = wr_fsm_req_ack_rd && ~wr_fsm_recv_ack_rd;

   // WADDR is sampled in RCLK domain.
   assign waddr_rd_nxt = waddr_sample_rd ? waddr_latch : waddr_rd;

   always_ff @(posedge rclk or negedge rrst_n) begin
      if (~rrst_n) begin
         waddr_rd <= '0;
      end else begin
         waddr_rd <= waddr_rd_nxt;
      end
   end

   // Get the acknowledge back into WCLK domain.  
   riv_synchronizer_2ff i_waddr_ack_cdc (
       .src_in(wr_fsm_recv_ack_rd),
       .dst_clk(wclk),
       .dst_rst_n(wrst_n),
       .dst_out(wr_fsm_recv_ack)
   );

   // -------------------------------------------------------------
   // Taking RADDR from RCLK domain to WCLK domain
   // -------------------------------------------------------------

   // RADDR is latched into a stable register during the LOAD state for transfer to the WCLK domain.
   assign raddr_latch_nxt = rd_fsm_load ? raddr : raddr_latch;

   always_ff @(posedge rclk or negedge rrst_n) begin
      if (~rrst_n) begin
         raddr_latch <= '0;
      end else begin
         raddr_latch <= raddr_latch_nxt;
      end
   end

   // Request the WCLK domain to sample RADDR when in REQ_ACK state.
   riv_synchronizer_2ff i_raddr_load_cdc (
       .src_in(rd_fsm_req_ack),
       .dst_clk(wclk),
       .dst_rst_n(wrst_n),
       .dst_out(rd_fsm_req_ack_wr)
   );

   // Generate an acknowledge signal in the WCLK domain to indicate that RADDR has been successfully sampled.
   always_ff @(posedge wclk or negedge wrst_n) begin
      if (~wrst_n) begin
         rd_fsm_recv_ack_wr <= 1'b0;
      end else begin
         rd_fsm_recv_ack_wr <= rd_fsm_req_ack_wr;
      end
   end

   // Detect positive edge of wr_fsm_req_ack_wr
   assign raddr_sample_wr = rd_fsm_req_ack_wr && ~rd_fsm_recv_ack_wr;

   // RADDR is sampled in WCLK domain.
   assign raddr_wr_nxt = raddr_sample_wr ? raddr_latch : raddr_wr;

   always_ff @(posedge wclk or negedge wrst_n) begin
      if (~wrst_n) begin
         raddr_wr <= '0;
      end else begin
         raddr_wr <= raddr_wr_nxt;
      end
   end

   // Get the acknowledge back into RCLK domain. 
   riv_synchronizer_2ff i_raddr_ack_cdc (
       .src_in(rd_fsm_recv_ack_wr),
       .dst_clk(rclk),
       .dst_rst_n(rrst_n),
       .dst_out(rd_fsm_recv_ack)
   );

endmodule  // riv_async_fifo_cdc

`endif  // RIV_ASYNC_FIFO_CDC_SV
