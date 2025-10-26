// SPDX-License-Identifier: None
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

`ifndef RIV_ASYNC_FIFO_CTL_SV
`define RIV_ASYNC_FIFO_CTL_SV

module riv_async_fifo_ctl #(
    parameter ADDR_WIDTH = 10
) (
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  en,
    output logic [ADDR_WIDTH-1:0] addr,
    output logic                  fsm_load,
    output logic                  fsm_req_ack,
    input  logic                  fsm_recv_ack
);

   // -------------------------------------------------------------
   // Type definition
   // -------------------------------------------------------------

   typedef enum bit [2:0] {
      RESET = 0,
      WAIT_FOR_EN = 1,
      LOAD = 2,
      WAIT_FOR_READY = 3,
      REQ_ACK = 4,
      WAIT_FOR_ACK = 5,
      UNKNOWN_6 = 6,
      UNKNOWN_7 = 7
   } fsm_t;

   // -------------------------------------------------------------
   // Declaration
   // -------------------------------------------------------------

   fsm_t fsm;
   fsm_t fsm_nxt;

   logic [ADDR_WIDTH-1:0] addr_nxt;

   // -------------------------------------------------------------
   // Address update logic
   // -------------------------------------------------------------

   assign addr_nxt = en ? addr + ADDR_WIDTH'(1'b1) : addr;

   always_ff @(posedge clk or negedge rst_n) begin
      if (~rst_n) begin
         addr <= '0;
      end else begin
         addr <= addr_nxt;
      end
   end

   // -------------------------------------------------------------
   // CDC state machine
   // -------------------------------------------------------------

   // State machine
   always_ff @(posedge clk or negedge rst_n) begin
      if (~rst_n) begin
         fsm <= RESET;
      end else begin
         fsm <= fsm_nxt;
      end
   end

   always_comb begin
      unique case (fsm)
         RESET:          fsm_nxt = WAIT_FOR_EN;
         WAIT_FOR_EN:    fsm_nxt = en ? LOAD : WAIT_FOR_EN;
         LOAD:           fsm_nxt = WAIT_FOR_READY;
         WAIT_FOR_READY: fsm_nxt = ~fsm_recv_ack ? REQ_ACK : WAIT_FOR_READY;
         REQ_ACK:        fsm_nxt = fsm_recv_ack ? LOAD : REQ_ACK;
         default:        fsm_nxt = RESET;
      endcase
   end

   assign fsm_load = (fsm == LOAD);
   assign fsm_req_ack = (fsm == REQ_ACK);

endmodule  // riv_async_fifo_ctl

`endif  // RIV_ASYNC_FIFO_CTL_SV
