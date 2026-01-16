# SPDX-License-Identifier: LicenseRef-LICENSE
# Copyright (c) 2025 Riverlane Ltd.
# Original authors: Aniket Datta

# Define clock and reset
create_clock clk_i -period 4
create_reset rst_n_i -sense low -clock clk_i

# Assume initial conditions for control signals during reset
sim_force [get_nets faw_boundary_i] -apply 0
sim_force [get_nets crc_boundary_i] -apply 0