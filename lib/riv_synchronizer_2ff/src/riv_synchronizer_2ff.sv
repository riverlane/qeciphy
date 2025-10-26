// SPDX-License-Identifier: None
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

`ifndef RIV_SYNCHRONIZER_2FF_SV
`define RIV_SYNCHRONIZER_2FF_SV

module riv_synchronizer_2ff (
    input logic src_in,  // signal to be synchronised
    input logic dst_clk,  // destination clock domain
    input logic dst_rst_n,  // destination domain active low reset
    output logic dst_out  // synchronised signal
);
   // -------------------------------------------------------------
   // Local declarations
   // -------------------------------------------------------------

   (* ASYNC_REG = "TRUE" *) logic [1:0] sync_stage_sf;

   // -------------------------------------------------------------
   // Logic
   // -------------------------------------------------------------

   always_ff @(posedge dst_clk or negedge dst_rst_n) begin
      if (~dst_rst_n) begin
         sync_stage_sf <= 2'h0;
      end else begin
         sync_stage_sf <= {sync_stage_sf[0], src_in};
      end
   end

   assign dst_out = sync_stage_sf[1];

endmodule  // riv_synchronizer_2ff

`endif  // RIV_SYNCHRONIZER_2FF_SV
