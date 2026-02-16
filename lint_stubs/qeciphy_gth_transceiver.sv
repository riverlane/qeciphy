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
    input gtwiz_userclk_tx_active_in,
    input gtwiz_userclk_rx_active_in,
    input gtwiz_reset_clk_freerun_in,
    input gtwiz_reset_all_in,
    input gtwiz_reset_tx_pll_and_datapath_in,
    input gtwiz_reset_tx_datapath_in,
    input gtwiz_reset_rx_pll_and_datapath_in,
    input gtwiz_reset_rx_datapath_in,
    output gtwiz_reset_rx_cdr_stable_out,
    output gtwiz_reset_tx_done_out,
    output gtwiz_reset_rx_done_out,
    input [31:0] gtwiz_userdata_tx_in,
    output [31:0] gtwiz_userdata_rx_out,
    input gtrefclk00_in,
    output qpll0outclk_out,
    output qpll0lock_out,
    output qpll0outrefclk_out,
    input gthrxn_in,
    input gthrxp_in,
    input rx8b10ben_in,
    input rxusrclk_in,
    input rxusrclk2_in,
    input tx8b10ben_in,
    input [15:0] txctrl0_in,
    input [15:0] txctrl1_in,
    input [7:0] txctrl2_in,
    input txusrclk_in,
    input txusrclk2_in,
    output gtpowergood_out,
    output gthtxn_out,
    output gthtxp_out,
    output [15:0] rxctrl0_out,
    output [15:0] rxctrl1_out,
    output [7:0] rxctrl2_out,
    output [7:0] rxctrl3_out,
    output rxoutclk_out,
    output rxpmaresetdone_out,
    output txoutclk_out,
    output txpmaresetdone_out,
    input rxcommadeten_in,
    input rxpcommaalignen_in,
    input rxmcommaalignen_in,
    output rxbyteisaligned_out,
    output rxbyterealign_out,
    output rxcommadet_out
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
