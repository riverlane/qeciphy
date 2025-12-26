# SPDX-License-Identifier: LicenseRef-LICENSE
# Copyright (c) 2025 Riverlane Ltd.
# Original authors: Aniket Datta

# Define clock and reset
create_clock clk_i -period 4
create_reset rst_n_i -sense low -clock clk_i