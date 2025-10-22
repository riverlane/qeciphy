# SPDX-License-Identifier: None
# Copyright (c) 2025 Riverlane Ltd.
# Original authors: Dogancan Davutoglu, Gargi-Sunil-RL, aniketEng

create_clock -period 8.0 -name gt_refclk [get_ports gt_refclk_in_p]
set_property PACKAGE_PIN U6   [get_ports gt_refclk_in_p]

create_clock -period 8.0 -name clk_freerun [get_ports clk_freerun_p];
set_property PACKAGE_PIN AC23 [get_ports clk_freerun_p]
set_property IOSTANDARD LVDS_25 [get_ports clk_freerun_p]

create_generated_clock -name rx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_rx_clks*inst/mmcm_adv_inst/CLKOUT0}]
create_generated_clock -name gt_rx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_rx_clks*inst/mmcm_adv_inst/CLKOUT1}]
create_generated_clock -name tx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_tx_clks*inst/mmcm_adv_inst/CLKOUT0}]
create_generated_clock -name gt_tx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_tx_clks*inst/mmcm_adv_inst/CLKOUT1}]

set_clock_groups -asynchronous -group [get_clocks gt_refclk] -group [get_clocks clk_freerun] -group [get_clocks {rx_clk gt_rx_clk}] -group [get_clocks {tx_clk gt_tx_clk}]
set_property CLOCK_DELAY_GROUP rx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_rx_clks/inst/clk_out || NAME =~ *QECIPHY*i_rx_clks/inst/clk_out_2x}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_tx_clks/inst/clk_out || NAME =~ *QECIPHY*i_tx_clks/inst/clk_out_2x}]

#Define multicycle path between sync clocks
set_multicycle_path 2 -setup -end -from [get_clocks rx_clk] -to [get_clocks gt_rx_clk]
set_multicycle_path 1 -hold  -end -from [get_clocks rx_clk] -to [get_clocks gt_rx_clk]
set_multicycle_path 2 -setup -start -from [get_clocks gt_rx_clk] -to [get_clocks rx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_rx_clk] -to [get_clocks rx_clk]
set_multicycle_path 2 -setup -end -from [get_clocks tx_clk] -to [get_clocks gt_tx_clk]
set_multicycle_path 1 -hold  -end -from [get_clocks tx_clk] -to [get_clocks gt_tx_clk]
set_multicycle_path 2 -setup -start -from [get_clocks gt_tx_clk] -to [get_clocks tx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_tx_clk] -to [get_clocks tx_clk]

# This constraint assigns the location GTXE2_CHANNEL_X0Y0 to cells matching the QECIPHY naming pattern.
# This ensures that we are using the correct SFP port
set_property LOC GTXE2_CHANNEL_X0Y0 [get_cells -hierarchical -filter {lib_cell =~ GTXE2_CHANNEL && NAME =~ *QECIPHY*}]

set_property IOSTANDARD LVCMOS25 [get_ports led[0]];
set_property IOSTANDARD LVCMOS25 [get_ports led[1]];

set_property PACKAGE_PIN AF19    [get_ports led[0]];
set_property PACKAGE_PIN AF23    [get_ports led[1]];
