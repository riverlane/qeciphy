// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

bind qeciphy_tx_boundary_gen qeciphy_tx_boundary_gen_checker i_qeciphy_tx_boundary_gen_bind (
    .clk_i                (clk_i),
    .rst_n_i              (rst_n_i),
    .faw_boundary_o       (faw_boundary_o),
    .almost_faw_boundary_o(almost_faw_boundary_o),
    .crc_boundary_o       (crc_boundary_o)
);

