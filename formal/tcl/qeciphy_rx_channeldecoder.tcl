# SPDX-License-Identifier: LicenseRef-LICENSE
# Copyright (c) 2026 Riverlane Ltd.
# Original authors: Aniket Datta

# Define clock and reset
create_clock clk_i -period 4
create_reset rst_n_i -sense low -clock clk_i

# Assume initial conditions for control signals during reset
sim_force [get_nets enable_i] -apply 0

# Disable CRC16 IBM3740 model checking (takes too long)
fvdisable *i_qeciphy_crc16_ibm3740_bind.p_crc16_step_matches_model_A*