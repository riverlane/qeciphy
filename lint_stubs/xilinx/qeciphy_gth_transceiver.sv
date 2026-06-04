// SPDX-License-Identifier: BSD-2-Clause
// -----------------------------------------------------------------------------
// File        : qeciphy_gth_transceiver.sv
// Description : Lint stub for Xilinx GTH transceiver module.
//               Declares the module interface for tooling convenience only.
//               No functional implementation is provided.
// 
// Copyright (c) 2025 Riverlane Ltd.
// This file is not affiliated with or endorsed by Xilinx Inc. or AMD.
// The module names and ports are reproduced solely for build compatibility.
// -----------------------------------------------------------------------------

module qeciphy_gth_transceiver (
    input logic gtwiz_userclk_tx_active_in,
    input logic gtwiz_userclk_rx_active_in,
    input logic gtwiz_reset_clk_freerun_in,
    input logic gtwiz_reset_all_in,
    input logic gtwiz_reset_tx_pll_and_datapath_in,
    input logic gtwiz_reset_tx_datapath_in,
    input logic gtwiz_reset_rx_pll_and_datapath_in,
    input logic gtwiz_reset_rx_datapath_in,
    output logic gtwiz_reset_rx_cdr_stable_out,
    output logic gtwiz_reset_tx_done_out,
    output logic gtwiz_reset_rx_done_out,
    input logic [31:0] gtwiz_userdata_tx_in,
    output logic [31:0] gtwiz_userdata_rx_out,
    input logic gtrefclk00_in,
    output logic qpll0outclk_out,
    output logic qpll0lock_out,
    output logic qpll0outrefclk_out,
    input logic gthrxn_in,
    input logic gthrxp_in,
    input logic rx8b10ben_in,
    input logic rxusrclk_in,
    input logic rxusrclk2_in,
    input logic tx8b10ben_in,
    input logic [15:0] txctrl0_in,
    input logic [15:0] txctrl1_in,
    input logic [7:0] txctrl2_in,
    input logic txusrclk_in,
    input logic txusrclk2_in,
    output logic gtpowergood_out,
    output logic gthtxn_out,
    output logic gthtxp_out,
    output logic [15:0] rxctrl0_out,
    output logic [15:0] rxctrl1_out,
    output logic [7:0] rxctrl2_out,
    output logic [7:0] rxctrl3_out,
    output logic rxoutclk_out,
    output logic rxpmaresetdone_out,
    output logic txoutclk_out,
    output logic txpmaresetdone_out,
    input logic rxcommadeten_in,
    input logic rxpcommaalignen_in,
    input logic rxmcommaalignen_in,
    output logic rxbyteisaligned_out,
    output logic rxbyterealign_out,
    output logic rxcommadet_out
);

   assign gtwiz_reset_rx_cdr_stable_out = '0;
   assign gtwiz_reset_tx_done_out = '0;
   assign gtwiz_reset_rx_done_out = '0;
   assign gtwiz_userdata_rx_out = '0;
   assign qpll0outclk_out = '0;
   assign qpll0lock_out = '0;
   assign qpll0outrefclk_out = '0;
   assign gtpowergood_out = '0;
   assign gthtxn_out = '0;
   assign gthtxp_out = '0;
   assign rxctrl0_out = '0;
   assign rxctrl1_out = '0;
   assign rxctrl2_out = '0;
   assign rxctrl3_out = '0;
   assign rxoutclk_out = '0;
   assign rxpmaresetdone_out = '0;
   assign txoutclk_out = '0;
   assign txpmaresetdone_out = '0;
   assign rxbyteisaligned_out = '0;
   assign rxbyterealign_out = '0;
   assign rxcommadet_out = '0;

endmodule
