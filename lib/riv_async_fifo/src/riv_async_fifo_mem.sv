// SPDX-License-Identifier: None
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

`ifndef RIV_ASYNC_FIFO_MEM_SV
`define RIV_ASYNC_FIFO_MEM_SV

module riv_async_fifo_mem #(
    parameter ADDR_WIDTH = 10,
    parameter DATA_WIDTH = 32
) (
    input  logic                  wclk,
    input  logic                  wen,
    input  logic [ADDR_WIDTH-1:0] waddr,
    input  logic [DATA_WIDTH-1:0] wdata,
    input  logic [ADDR_WIDTH-1:0] raddr,
    output logic [DATA_WIDTH-1:0] rdata
);

   // -------------------------------------------------------------
   // Declaration
   // -------------------------------------------------------------

   logic [DATA_WIDTH-1:0] mem[0:(1<<ADDR_WIDTH)-1];

   // -------------------------------------------------------------
   // Write logic
   // -------------------------------------------------------------

   always_ff @(posedge wclk) begin
      if (wen) begin
         mem[waddr] <= wdata;
      end
   end

   // -------------------------------------------------------------
   // Read logic
   // -------------------------------------------------------------

   assign rdata = mem[raddr];

endmodule  // riv_async_fifo_mem

`endif  // RIV_ASYNC_FIFO_MEM_SV
