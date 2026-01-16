// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

bind qeciphy_rx_channeldecoder qeciphy_rx_channeldecoder_checker i_qeciphy_rx_channeldecoder_bind (
    .clk_i           (clk_i),
    .rst_n_i         (rst_n_i),
    .tdata_i         (tdata_i),
    .tdata_o         (tdata_o),
    .tvalid_o        (tvalid_o),
    .enable_i        (enable_i),
    .rx_fault_fatal_o(rx_fault_fatal_o),
    .rx_error_code_o (rx_error_code_o),
    .rx_rdy_o        (rx_rdy_o),
    .remote_rx_rdy_o (remote_rx_rdy_o)
);
