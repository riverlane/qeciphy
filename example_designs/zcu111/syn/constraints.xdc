# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2025 Riverlane Ltd.
# Original authors: Dogancan Davutoglu, Aniket Datta, Gargi Sunil

create_clock -period 6.400 -name gt_refclk [get_ports gt_refclk_in_p]
set_property PACKAGE_PIN W33 [get_ports gt_refclk_in_p]

# -------------------------------------------------------------------------
# QECIPHY instance 0 clocks
# -------------------------------------------------------------------------
create_generated_clock -name rx_clk [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name gt_rx_clk [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/RXOUTCLK}]
create_generated_clock -name tx_clk [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name gt_tx_clk [get_pins -hierarchical -filter {NAME =~ *i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]

set_clock_groups -asynchronous -group [get_clocks gt_refclk] -group [get_clocks {rx_clk gt_rx_clk}] -group [get_clocks {tx_clk gt_tx_clk}]
set_property CLOCK_DELAY_GROUP rx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/rx_clk_o || NAME =~ *i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/rx_clk_2x_o}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/tx_clk_o || NAME =~ *i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/tx_clk_2x_o}]

#Define multicycle path between sync clocks
set_multicycle_path -setup -end -from [get_clocks rx_clk] -to [get_clocks gt_rx_clk] 2
set_multicycle_path -hold -end -from [get_clocks rx_clk] -to [get_clocks gt_rx_clk] 1
set_multicycle_path -setup -start -from [get_clocks gt_rx_clk] -to [get_clocks rx_clk] 2
set_multicycle_path -hold -start -from [get_clocks gt_rx_clk] -to [get_clocks rx_clk] 1
set_multicycle_path -setup -end -from [get_clocks tx_clk] -to [get_clocks gt_tx_clk] 2
set_multicycle_path -hold -end -from [get_clocks tx_clk] -to [get_clocks gt_tx_clk] 1
set_multicycle_path -setup -start -from [get_clocks gt_tx_clk] -to [get_clocks tx_clk] 2
set_multicycle_path -hold -start -from [get_clocks gt_tx_clk] -to [get_clocks tx_clk] 1

set_property IOSTANDARD LVCMOS18 [get_ports {led[0]}]
set_property IOSTANDARD LVCMOS18 [get_ports {led[1]}]
set_property IOSTANDARD LVCMOS18 [get_ports {led[2]}]

set_property PACKAGE_PIN AR13 [get_ports {led[0]}]
set_property PACKAGE_PIN AP13 [get_ports {led[1]}]
set_property PACKAGE_PIN AR16 [get_ports {led[2]}]

set_property IOSTANDARD LVCMOS12 [get_ports {SFP_tx_enable[0]}]
set_property IOSTANDARD LVCMOS12 [get_ports {SFP_tx_enable[1]}]
set_property IOSTANDARD LVCMOS12 [get_ports {SFP_tx_enable[2]}]
set_property IOSTANDARD LVCMOS12 [get_ports {SFP_tx_enable[3]}]

set_property PACKAGE_PIN G12 [get_ports {SFP_tx_enable[0]}]
set_property PACKAGE_PIN G10 [get_ports {SFP_tx_enable[1]}]
set_property PACKAGE_PIN K12 [get_ports {SFP_tx_enable[2]}]
set_property PACKAGE_PIN J7  [get_ports {SFP_tx_enable[3]}]
