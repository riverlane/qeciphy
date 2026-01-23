// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Alex Crownshaw

bind riv_counter riv_counter_checker i_riv_counter_bind (
    .clk   (clk),
    .rst_n (rst_n),
    .value (value),
    .load  (load),
    .enable(enable),
    .done  (done)
);
