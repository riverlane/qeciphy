// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

bind qeciphy_crc_compute qeciphy_crc_compute_checker i_qeciphy_crc_compute_bind (
    .clk_i(clk_i),
    .rst_n_i(rst_n_i),
    .faw_boundary_i(faw_boundary_i),
    .crc_boundary_i(crc_boundary_i),
    .tdata_i(tdata_i),

    .crc01_rst_n(crc01_rst_n),
    .crc23_rst_n(crc23_rst_n),
    .crc45_rst_n(crc45_rst_n),
    .crcvw_rst_n(crcvw_rst_n),

    .crc01_en(crc01_en),
    .crc23_en(crc23_en),
    .crc45_en(crc45_en),
    .crcvw_en(crcvw_en),

    .crc01_valid(crc01_valid),
    .crc23_valid(crc23_valid),
    .crc45_valid(crc45_valid),
    .crcvw_valid(crcvw_valid),

    .crc01_calc(crc01_calc),
    .crc23_calc(crc23_calc),
    .crc45_calc(crc45_calc),
    .crcvw_calc(crcvw_calc),

    .crc_valid_o(crc_valid_o),
    .crc01_o(crc01_o),
    .crc23_o(crc23_o),
    .crc45_o(crc45_o),
    .crcvw_o(crcvw_o)
);
