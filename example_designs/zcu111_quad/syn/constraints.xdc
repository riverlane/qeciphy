# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2026 Riverlane Ltd.
# Original authors: Evan Sun
#
# 4-lane example design on the SFP0-SFP3 cages: bank 128's GT quad
# (GTYE4_CHANNEL_X0Y4-X0Y7, GTYE4_COMMON_X0Y1). Refclk is the Si570
# (MGTREFCLK1_129/USER_MGT_SI570_CLOCK), which must be set to 156.25 MHz.
#
# Each lane's LOC places its channel; the GT RX/TX package pins follow from
# it. Lanes are written out individually since XDC doesn't support foreach.

create_clock -period 6.4 -name gt_refclk [get_ports gt_refclk_in_p]
set_property PACKAGE_PIN V31 [get_ports gt_refclk_in_p]
set_property PACKAGE_PIN V32 [get_ports gt_refclk_in_n]

# ---- Lane 0: GTYE4_CHANNEL_X0Y4 (SFP0) ----
set_property LOC GTYE4_CHANNEL_X0Y4 [get_cells -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[0].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST}]

create_generated_clock -name rx_clk_0    [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[0].i_QECIPHY*i_qeciphy_gt_wrapper*i_qeciphy_gt_xilinx/gen_GTY_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name gt_rx_clk_0 [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[0].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/RXOUTCLK}]
create_generated_clock -name tx_clk_0    [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[0].i_QECIPHY*i_qeciphy_gt_wrapper*i_qeciphy_gt_xilinx/gen_GTY_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name gt_tx_clk_0 [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[0].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]

set_clock_groups -asynchronous \
    -group [get_clocks gt_refclk] \
    -group [get_clocks {rx_clk_0 gt_rx_clk_0}] \
    -group [get_clocks {tx_clk_0 gt_tx_clk_0}]

set_property CLOCK_DELAY_GROUP rx_clk_dly_grp_0 [get_nets -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[0].i_QECIPHY*i_qeciphy_gt_wrapper/rx_clk_o || NAME =~ *i_QECIPHY_QUAD/gen_lane[0].i_QECIPHY*i_qeciphy_gt_wrapper/rx_clk_2x_o}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp_0 [get_nets -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[0].i_QECIPHY*i_qeciphy_gt_wrapper/tx_clk_o || NAME =~ *i_QECIPHY_QUAD/gen_lane[0].i_QECIPHY*i_qeciphy_gt_wrapper/tx_clk_2x_o}]

# Multicycle path between sync clocks
set_multicycle_path 2 -setup -end   -from [get_clocks rx_clk_0]    -to [get_clocks gt_rx_clk_0]
set_multicycle_path 1 -hold  -end   -from [get_clocks rx_clk_0]    -to [get_clocks gt_rx_clk_0]
set_multicycle_path 2 -setup -start -from [get_clocks gt_rx_clk_0] -to [get_clocks rx_clk_0]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_rx_clk_0] -to [get_clocks rx_clk_0]
set_multicycle_path 2 -setup -end   -from [get_clocks tx_clk_0]    -to [get_clocks gt_tx_clk_0]
set_multicycle_path 1 -hold  -end   -from [get_clocks tx_clk_0]    -to [get_clocks gt_tx_clk_0]
set_multicycle_path 2 -setup -start -from [get_clocks gt_tx_clk_0] -to [get_clocks tx_clk_0]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_tx_clk_0] -to [get_clocks tx_clk_0]

# ---- Lane 1: GTYE4_CHANNEL_X0Y5 (SFP1) ----
set_property LOC GTYE4_CHANNEL_X0Y5 [get_cells -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[1].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST}]

create_generated_clock -name rx_clk_1    [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[1].i_QECIPHY*i_qeciphy_gt_wrapper*i_qeciphy_gt_xilinx/gen_GTY_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name gt_rx_clk_1 [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[1].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/RXOUTCLK}]
create_generated_clock -name tx_clk_1    [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[1].i_QECIPHY*i_qeciphy_gt_wrapper*i_qeciphy_gt_xilinx/gen_GTY_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name gt_tx_clk_1 [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[1].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]

set_clock_groups -asynchronous \
    -group [get_clocks gt_refclk] \
    -group [get_clocks {rx_clk_1 gt_rx_clk_1}] \
    -group [get_clocks {tx_clk_1 gt_tx_clk_1}]

set_property CLOCK_DELAY_GROUP rx_clk_dly_grp_1 [get_nets -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[1].i_QECIPHY*i_qeciphy_gt_wrapper/rx_clk_o || NAME =~ *i_QECIPHY_QUAD/gen_lane[1].i_QECIPHY*i_qeciphy_gt_wrapper/rx_clk_2x_o}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp_1 [get_nets -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[1].i_QECIPHY*i_qeciphy_gt_wrapper/tx_clk_o || NAME =~ *i_QECIPHY_QUAD/gen_lane[1].i_QECIPHY*i_qeciphy_gt_wrapper/tx_clk_2x_o}]

# Multicycle path between sync clocks
set_multicycle_path 2 -setup -end   -from [get_clocks rx_clk_1]    -to [get_clocks gt_rx_clk_1]
set_multicycle_path 1 -hold  -end   -from [get_clocks rx_clk_1]    -to [get_clocks gt_rx_clk_1]
set_multicycle_path 2 -setup -start -from [get_clocks gt_rx_clk_1] -to [get_clocks rx_clk_1]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_rx_clk_1] -to [get_clocks rx_clk_1]
set_multicycle_path 2 -setup -end   -from [get_clocks tx_clk_1]    -to [get_clocks gt_tx_clk_1]
set_multicycle_path 1 -hold  -end   -from [get_clocks tx_clk_1]    -to [get_clocks gt_tx_clk_1]
set_multicycle_path 2 -setup -start -from [get_clocks gt_tx_clk_1] -to [get_clocks tx_clk_1]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_tx_clk_1] -to [get_clocks tx_clk_1]

# ---- Lane 2: GTYE4_CHANNEL_X0Y6 (SFP2) ----
set_property LOC GTYE4_CHANNEL_X0Y6 [get_cells -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[2].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST}]

create_generated_clock -name rx_clk_2    [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[2].i_QECIPHY*i_qeciphy_gt_wrapper*i_qeciphy_gt_xilinx/gen_GTY_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name gt_rx_clk_2 [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[2].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/RXOUTCLK}]
create_generated_clock -name tx_clk_2    [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[2].i_QECIPHY*i_qeciphy_gt_wrapper*i_qeciphy_gt_xilinx/gen_GTY_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name gt_tx_clk_2 [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[2].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]

set_clock_groups -asynchronous \
    -group [get_clocks gt_refclk] \
    -group [get_clocks {rx_clk_2 gt_rx_clk_2}] \
    -group [get_clocks {tx_clk_2 gt_tx_clk_2}]

set_property CLOCK_DELAY_GROUP rx_clk_dly_grp_2 [get_nets -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[2].i_QECIPHY*i_qeciphy_gt_wrapper/rx_clk_o || NAME =~ *i_QECIPHY_QUAD/gen_lane[2].i_QECIPHY*i_qeciphy_gt_wrapper/rx_clk_2x_o}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp_2 [get_nets -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[2].i_QECIPHY*i_qeciphy_gt_wrapper/tx_clk_o || NAME =~ *i_QECIPHY_QUAD/gen_lane[2].i_QECIPHY*i_qeciphy_gt_wrapper/tx_clk_2x_o}]

# Multicycle path between sync clocks
set_multicycle_path 2 -setup -end   -from [get_clocks rx_clk_2]    -to [get_clocks gt_rx_clk_2]
set_multicycle_path 1 -hold  -end   -from [get_clocks rx_clk_2]    -to [get_clocks gt_rx_clk_2]
set_multicycle_path 2 -setup -start -from [get_clocks gt_rx_clk_2] -to [get_clocks rx_clk_2]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_rx_clk_2] -to [get_clocks rx_clk_2]
set_multicycle_path 2 -setup -end   -from [get_clocks tx_clk_2]    -to [get_clocks gt_tx_clk_2]
set_multicycle_path 1 -hold  -end   -from [get_clocks tx_clk_2]    -to [get_clocks gt_tx_clk_2]
set_multicycle_path 2 -setup -start -from [get_clocks gt_tx_clk_2] -to [get_clocks tx_clk_2]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_tx_clk_2] -to [get_clocks tx_clk_2]

# ---- Lane 3: GTYE4_CHANNEL_X0Y7 (SFP3) ----
set_property LOC GTYE4_CHANNEL_X0Y7 [get_cells -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[3].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST}]

create_generated_clock -name rx_clk_3    [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[3].i_QECIPHY*i_qeciphy_gt_wrapper*i_qeciphy_gt_xilinx/gen_GTY_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name gt_rx_clk_3 [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[3].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/RXOUTCLK}]
create_generated_clock -name tx_clk_3    [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[3].i_QECIPHY*i_qeciphy_gt_wrapper*i_qeciphy_gt_xilinx/gen_GTY_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name gt_tx_clk_3 [get_pins -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[3].i_QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]

set_clock_groups -asynchronous \
    -group [get_clocks gt_refclk] \
    -group [get_clocks {rx_clk_3 gt_rx_clk_3}] \
    -group [get_clocks {tx_clk_3 gt_tx_clk_3}]

set_property CLOCK_DELAY_GROUP rx_clk_dly_grp_3 [get_nets -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[3].i_QECIPHY*i_qeciphy_gt_wrapper/rx_clk_o || NAME =~ *i_QECIPHY_QUAD/gen_lane[3].i_QECIPHY*i_qeciphy_gt_wrapper/rx_clk_2x_o}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp_3 [get_nets -hierarchical -filter \
    {NAME =~ *i_QECIPHY_QUAD/gen_lane[3].i_QECIPHY*i_qeciphy_gt_wrapper/tx_clk_o || NAME =~ *i_QECIPHY_QUAD/gen_lane[3].i_QECIPHY*i_qeciphy_gt_wrapper/tx_clk_2x_o}]

# Multicycle path between sync clocks
set_multicycle_path 2 -setup -end   -from [get_clocks rx_clk_3]    -to [get_clocks gt_rx_clk_3]
set_multicycle_path 1 -hold  -end   -from [get_clocks rx_clk_3]    -to [get_clocks gt_rx_clk_3]
set_multicycle_path 2 -setup -start -from [get_clocks gt_rx_clk_3] -to [get_clocks rx_clk_3]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_rx_clk_3] -to [get_clocks rx_clk_3]
set_multicycle_path 2 -setup -end   -from [get_clocks tx_clk_3]    -to [get_clocks gt_tx_clk_3]
set_multicycle_path 1 -hold  -end   -from [get_clocks tx_clk_3]    -to [get_clocks gt_tx_clk_3]
set_multicycle_path 2 -setup -start -from [get_clocks gt_tx_clk_3] -to [get_clocks tx_clk_3]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_tx_clk_3] -to [get_clocks tx_clk_3]

set_property IOSTANDARD LVCMOS18 [get_ports led[0]]
set_property IOSTANDARD LVCMOS18 [get_ports led[1]]
set_property IOSTANDARD LVCMOS18 [get_ports led[2]]

set_property PACKAGE_PIN AR13 [get_ports led[0]]
set_property PACKAGE_PIN AP13 [get_ports led[1]]
set_property PACKAGE_PIN AR16 [get_ports led[2]]

set_property IOSTANDARD LVCMOS12 [get_ports SFP_tx_enable[0]]
set_property IOSTANDARD LVCMOS12 [get_ports SFP_tx_enable[1]]
set_property IOSTANDARD LVCMOS12 [get_ports SFP_tx_enable[2]]
set_property IOSTANDARD LVCMOS12 [get_ports SFP_tx_enable[3]]

set_property PACKAGE_PIN G12 [get_ports SFP_tx_enable[0]]
set_property PACKAGE_PIN G10 [get_ports SFP_tx_enable[1]]
set_property PACKAGE_PIN K12 [get_ports SFP_tx_enable[2]]
set_property PACKAGE_PIN J7  [get_ports SFP_tx_enable[3]]
