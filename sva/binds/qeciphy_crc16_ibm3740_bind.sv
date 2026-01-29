// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

bind qeciphy_crc16_ibm3740 qeciphy_crc16_ibm3740_checker i_qeciphy_crc16_ibm3740_bind (
    .clk_i      (clk_i),
    .rst_n_i    (rst_n_i),
    .tdata_i    (tdata_i),
    .tvalid_i   (tvalid_i),
    .crc_o      (crc_o),
    .crc_valid_o(crc_valid_o)
);
