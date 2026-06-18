# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2025 Riverlane Ltd.

create_clock -period 6.4 -name gt_refclk [get_ports gt_refclk_in_p]
set_property PACKAGE_PIN W9 [get_ports gt_refclk_in_p]

# Clocks for i_QECIPHY_0 (GT X1Y48)
create_generated_clock -name rx_clk_0    [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY_0*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name gt_rx_clk_0 [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY_0*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/RXOUTCLK}]
create_generated_clock -name tx_clk_0    [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY_0*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name gt_tx_clk_0 [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY_0*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]

# Clocks for i_QECIPHY_1 (GT X1Y52)
create_generated_clock -name rx_clk_1    [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY_1*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name gt_rx_clk_1 [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY_1*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/RXOUTCLK}]
create_generated_clock -name tx_clk_1    [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY_1*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name gt_tx_clk_1 [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY_1*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]

set_clock_groups -asynchronous \
    -group [get_clocks gt_refclk] \
    -group [get_clocks {rx_clk_0 gt_rx_clk_0}] \
    -group [get_clocks {tx_clk_0 gt_tx_clk_0}] \
    -group [get_clocks {rx_clk_1 gt_rx_clk_1}] \
    -group [get_clocks {tx_clk_1 gt_tx_clk_1}]

set_property CLOCK_DELAY_GROUP rx_clk_0_dly_grp [get_nets -hierarchical -filter {NAME =~ *i_QECIPHY_0*i_qeciphy_gt_wrapper/rx_clk_o || NAME =~ *i_QECIPHY_0*i_qeciphy_gt_wrapper/rx_clk_2x_o}]
set_property CLOCK_DELAY_GROUP tx_clk_0_dly_grp [get_nets -hierarchical -filter {NAME =~ *i_QECIPHY_0*i_qeciphy_gt_wrapper/tx_clk_o || NAME =~ *i_QECIPHY_0*i_qeciphy_gt_wrapper/tx_clk_2x_o}]
set_property CLOCK_DELAY_GROUP rx_clk_1_dly_grp [get_nets -hierarchical -filter {NAME =~ *i_QECIPHY_1*i_qeciphy_gt_wrapper/rx_clk_o || NAME =~ *i_QECIPHY_1*i_qeciphy_gt_wrapper/rx_clk_2x_o}]
set_property CLOCK_DELAY_GROUP tx_clk_1_dly_grp [get_nets -hierarchical -filter {NAME =~ *i_QECIPHY_1*i_qeciphy_gt_wrapper/tx_clk_o || NAME =~ *i_QECIPHY_1*i_qeciphy_gt_wrapper/tx_clk_2x_o}]

# Multicycle paths for i_QECIPHY_0
set_multicycle_path 2 -setup -end   -from [get_clocks rx_clk_0] -to [get_clocks gt_rx_clk_0]
set_multicycle_path 1 -hold  -end   -from [get_clocks rx_clk_0] -to [get_clocks gt_rx_clk_0]
set_multicycle_path 2 -setup -start -from [get_clocks gt_rx_clk_0] -to [get_clocks rx_clk_0]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_rx_clk_0] -to [get_clocks rx_clk_0]
set_multicycle_path 2 -setup -end   -from [get_clocks tx_clk_0] -to [get_clocks gt_tx_clk_0]
set_multicycle_path 1 -hold  -end   -from [get_clocks tx_clk_0] -to [get_clocks gt_tx_clk_0]
set_multicycle_path 2 -setup -start -from [get_clocks gt_tx_clk_0] -to [get_clocks tx_clk_0]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_tx_clk_0] -to [get_clocks tx_clk_0]

# Multicycle paths for i_QECIPHY_1
set_multicycle_path 2 -setup -end   -from [get_clocks rx_clk_1] -to [get_clocks gt_rx_clk_1]
set_multicycle_path 1 -hold  -end   -from [get_clocks rx_clk_1] -to [get_clocks gt_rx_clk_1]
set_multicycle_path 2 -setup -start -from [get_clocks gt_rx_clk_1] -to [get_clocks rx_clk_1]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_rx_clk_1] -to [get_clocks rx_clk_1]
set_multicycle_path 2 -setup -end   -from [get_clocks tx_clk_1] -to [get_clocks gt_tx_clk_1]
set_multicycle_path 1 -hold  -end   -from [get_clocks tx_clk_1] -to [get_clocks gt_tx_clk_1]
set_multicycle_path 2 -setup -start -from [get_clocks gt_tx_clk_1] -to [get_clocks tx_clk_1]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_tx_clk_1] -to [get_clocks tx_clk_1]

# GT location constraints — place each instance at its assigned channel
set_property LOC GTYE4_CHANNEL_X1Y48 [get_cells -hierarchical -filter {lib_cell =~ GTYE4_CHANNEL && NAME =~ *i_QECIPHY_0*}]
set_property LOC GTYE4_CHANNEL_X1Y52 [get_cells -hierarchical -filter {lib_cell =~ GTYE4_CHANNEL && NAME =~ *i_QECIPHY_1*}]

set_property IOSTANDARD LVCMOS18 [get_ports led[0]];
set_property IOSTANDARD LVCMOS18 [get_ports led[1]];
set_property IOSTANDARD LVCMOS18 [get_ports led[2]];
set_property IOSTANDARD LVCMOS18 [get_ports led[3]];

set_property PACKAGE_PIN AT32 [get_ports led[0]];
set_property PACKAGE_PIN AV34 [get_ports led[1]];
set_property PACKAGE_PIN AY30 [get_ports led[2]];
set_property PACKAGE_PIN BB32 [get_ports led[3]];
