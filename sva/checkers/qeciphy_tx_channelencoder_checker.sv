// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_tx_channelencoder_checker (
    input logic        clk_i,
    input logic        rst_n_i,
    input logic [63:0] s_axis_tdata_i,
    input logic        s_axis_tvalid_i,
    input logic        s_axis_tready_o,
    input logic [63:0] m_axis_tdata_o,
    input logic        m_axis_tdata_isfaw_o,
    input logic        link_enable_i,
    input logic        data_enable_i,
    input logic        rx_rdy_i
);

   localparam int TDATA_LATENCY = 3;

   // Ensure that s_axis_tready_o is reachable
   cover_s_axis_tready_o_C :
   cover property (@(posedge clk_i) s_axis_tready_o);

   // m_axis_tdata_o reflects s_axis_tdata_i with a latency of TDATA_LATENCY cycles when both link_enable_i and data_enable_i are high
   property p_m_axis_tdata_o_from_s_axis_tdata_i;
      logic [63:0] expected_data;
      @(posedge clk_i) disable iff (!rst_n_i) (link_enable_i && data_enable_i && s_axis_tvalid_i && s_axis_tready_o,
      expected_data = s_axis_tdata_i
      ) |-> ##TDATA_LATENCY(m_axis_tdata_o == expected_data);
   endproperty

   m_axis_tdata_o_from_s_axis_tdata_i_A :
   assert property (p_m_axis_tdata_o_from_s_axis_tdata_i)
   else $fatal(1, "m_axis_tdata_o does not match s_axis_tdata_i with expected latency when link and data are enabled.");

endmodule
