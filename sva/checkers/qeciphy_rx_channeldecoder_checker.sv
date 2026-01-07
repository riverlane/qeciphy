// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

`include "qeciphy_pkg.sv"

module qeciphy_rx_channeldecoder_checker (
    input logic        clk_i,
    input logic        rst_n_i,
    input logic [63:0] tdata_i,
    input logic [63:0] tdata_o,
    input logic        tvalid_o,
    input logic        enable_i,
    input logic        rx_fault_fatal_o,
    input logic [ 3:0] rx_error_code_o,
    input logic        rx_rdy_o,
    input logic        remote_rx_rdy_o
);

   import qeciphy_pkg::*;

   localparam int TDATA_LATENCY = 11;

   // Ensure that rx_rdy_o is reachable
   cover_rx_rdy_o_C :
   cover property (@(posedge clk_i) rx_rdy_o);

   // Ensure that remote_rx_rdy_o is reachable
   cover_remote_rx_rdy_o_C :
   cover property (@(posedge clk_i) remote_rx_rdy_o);

   // Ensure that rx_fault_fatal_o is reachable
   cover_rx_fault_fatal_o_C :
   cover property (@(posedge clk_i) rx_fault_fatal_o);

   // Ensure that rx_error_code_o == FAW_ERROR is reachable
   cover_rx_error_code_faw_C :
   cover property (@(posedge clk_i) qeciphy_error_t'(rx_error_code_o) == FAW_ERROR);

   // Ensure that rx_error_code_o == CRC_ERROR is reachable
   cover_rx_error_code_crc_C :
   cover property (@(posedge clk_i) qeciphy_error_t'(rx_error_code_o) == CRC_ERROR);

   // Ensure that tvalid_o is reachable
   cover_tvalid_o_C :
   cover property (@(posedge clk_i) tvalid_o);

   // tdata_o reflects tdata_i with a latency of TDATA_LATENCY cycles when tvalid_o is high
   property p_tdata_o_from_tdata_i;
      @(posedge clk_i) disable iff (!rst_n_i) tvalid_o |-> (tdata_o == $past(
          tdata_i, TDATA_LATENCY
      ));
   endproperty

   tdata_o_from_tdata_i_A :
   assert property (p_tdata_o_from_tdata_i);

endmodule
