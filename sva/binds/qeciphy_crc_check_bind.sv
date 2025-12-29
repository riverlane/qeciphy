// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

bind qeciphy_crc_check qeciphy_crc_check_checker i_qeciphy_crc_check_checker_bind (
    .clk_i         (clk_i),
    .rst_n_i       (rst_n_i),
    .crc_boundary_i(crc_boundary_i),
    .tdata_i       (tdata_i),
    .crc01_i       (crc01_i),
    .crc23_i       (crc23_i),
    .crc45_i       (crc45_i),
    .crcvw_i       (crcvw_i),
    .crc_valid_i   (crc_valid_i),
    .crc_error_o   (crc_error_o),
    .check_done_o  (check_done_o)
);
