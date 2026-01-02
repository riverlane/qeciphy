// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

bind qeciphy_rx_boundary_gen qeciphy_rx_boundary_gen_checker i_qeciphy_rx_boundary_gen_bind (
    .clk_i         (clk_i),
    .rst_n_i       (rst_n_i),
    .tdata_i       (tdata_i),
    .tdata_o       (tdata_o),
    .enable_i      (enable_i),
    .locked_o      (locked_o),
    .faw_boundary_o(faw_boundary_o),
    .crc_boundary_o(crc_boundary_o)
);
