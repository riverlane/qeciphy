# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2026 Riverlane Ltd.
# Original authors: Aniket Datta

# Define clock and reset
create_clock clk_i -period 4
create_reset rst_n_i -sense low -clock clk_i
