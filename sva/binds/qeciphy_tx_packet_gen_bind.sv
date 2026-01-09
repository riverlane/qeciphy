// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

bind qeciphy_tx_packet_gen qeciphy_tx_packet_gen_checker i_qeciphy_tx_packet_gen_bind (
    .clk_i          (clk_i),
    .rst_n_i        (rst_n_i),
    .faw_boundary_i (faw_boundary_i),
    .crc_boundary_i (crc_boundary_i),
    .s_axis_tdata_i (s_axis_tdata_i),
    .s_axis_tvalid_i(s_axis_tvalid_i),
    .s_axis_tready_o(s_axis_tready_o),
    .m_axis_tdata_o (m_axis_tdata_o),
    .tx_off_i       (tx_off_i),
    .tx_idle_i      (tx_idle_i),
    .tx_active_i    (tx_active_i),
    .rx_rdy_i       (rx_rdy_i),
    .crc01_calc     (crc01_calc),
    .crc23_calc     (crc23_calc),
    .crc45_calc     (crc45_calc),
    .crcvw_calc     (crcvw_calc),
    .crc_valid      (crc_valid)
);

