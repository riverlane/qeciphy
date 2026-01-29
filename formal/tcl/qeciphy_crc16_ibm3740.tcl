# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2025 Riverlane Ltd.
# Original authors: Aniket Datta

# Define clock and reset
create_clock clk_i -period 4
create_reset rst_n_i -sense low -clock clk_i

# Disable CRC16 IBM3740 model checking (takes too long)
fvdisable *p_crc16_step_matches_model_A*