// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

bind qeciphy_rx_controller qeciphy_rx_controller_checker i_qeciphy_rx_controller_bind (
    .clk_i           (clk_i),
    .rst_n_i         (rst_n_i),
    .enable_i        (enable_i),
    .rx_locked_i     (rx_locked_i),
    .crc_err_i       (crc_err_i),
    .faw_err_i       (faw_err_i),
    .rx_enable_o     (rx_enable_o),
    .rx_rdy_o        (rx_rdy_o),
    .rx_fault_fatal_o(rx_fault_fatal_o),
    .rx_error_code_o (rx_error_code_o)
);
