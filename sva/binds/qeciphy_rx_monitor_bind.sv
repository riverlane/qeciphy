// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

bind qeciphy_rx_monitor qeciphy_rx_monitor_checker i_qeciphy_rx_monitor_bind (
    .clk_i          (clk_i),
    .rst_n_i        (rst_n_i),
    .tdata_i        (tdata_i),
    .tdata_o        (tdata_o),
    .tvalid_o       (tvalid_o),
    .enable_i       (enable_i),
    .faw_boundary_i (faw_boundary_i),
    .crc_boundary_i (crc_boundary_i),
    .crc_error_o    (crc_error_o),
    .faw_error_o    (faw_error_o),
    .remote_rx_rdy_o(remote_rx_rdy_o),
    .crc_check_done (crc_check_done),
    .crc_check_error(crc_check_error)
);
