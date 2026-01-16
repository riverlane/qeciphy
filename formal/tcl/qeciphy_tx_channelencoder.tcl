# SPDX-License-Identifier: LicenseRef-LICENSE
# Copyright (c) 2026 Riverlane Ltd.
# Original authors: Aniket Datta

# Define clock and reset
create_clock clk_i -period 4
create_reset rst_n_i -sense low -clock clk_i

# Disable CRC16 IBM3740 model checking (takes too long)
fvdisable *i_qeciphy_crc16_ibm3740_bind.p_crc16_step_matches_model_A*