// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_tx_channelencoder_harness;

   logic clk_i;
   logic rst_n_i;
   logic [63:0] s_axis_tdata_i;
   logic s_axis_tvalid_i;
   logic s_axis_tready_o;
   logic [63:0] m_axis_tdata_o;
   logic m_axis_tdata_isfaw_o;
   logic link_enable_i;
   logic data_enable_i;
   logic rx_rdy_i;

   qeciphy_tx_channelencoder dut (.*);

   // No input assumptions necessary

endmodule

