// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

bind qeciphy_tx_channelencoder qeciphy_tx_channelencoder_checker i_qeciphy_tx_channelencoder_bind (
    .clk_i               (clk_i),
    .rst_n_i             (rst_n_i),
    .s_axis_tdata_i      (s_axis_tdata_i),
    .s_axis_tvalid_i     (s_axis_tvalid_i),
    .s_axis_tready_o     (s_axis_tready_o),
    .m_axis_tdata_o      (m_axis_tdata_o),
    .m_axis_tdata_isfaw_o(m_axis_tdata_isfaw_o),
    .link_enable_i       (link_enable_i),
    .data_enable_i       (data_enable_i),
    .rx_rdy_i            (rx_rdy_i)
);
