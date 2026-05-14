#SPDX-License-Identifier: BSD-2-Clause
#Copyright (c) 2026 Riverlane Ltd.

# False paths for async reset and async reset release to RX and TX clock domains
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|gen_etile.transceiver_inst|xcvrnphy_fme_0|g_pma_rsfec_reset.g_auto_reset.reset_ip_auto_etile_inst|reset_control_inst|g_rx.g_rx[0].g_rx.counter_rx_ready|r_reset}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|rx_ready_sync_ff[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|gen_etile.transceiver_inst|xcvrnphy_fme_0|g_pma_rsfec_reset.g_auto_reset.reset_ip_auto_etile_inst|reset_control_inst|g_tx.g_tx[0].g_tx.counter_tx_ready|r_reset}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tx_ready_sync_ff[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|gen_etile.transceiver_inst|xcvrnphy_fme_0|g_pma_rsfec_reset.g_auto_reset.reset_ip_auto_etile_inst|reset_control_inst|g_rx.g_rx[0].g_rx.counter_rx_ready|r_reset}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|rx_ready_2x_sync_ff[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|gen_etile.transceiver_inst|xcvrnphy_fme_0|g_pma_rsfec_reset.g_auto_reset.reset_ip_auto_etile_inst|reset_control_inst|g_tx.g_tx[0].g_tx.counter_tx_ready|r_reset}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tx_ready_2x_sync_ff[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_resetcontroller|i_cdc_gt_rst_n_o|sync_stage_sf[1]}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tx_reset_sync_ff[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_resetcontroller|i_cdc_gt_rst_n_o|sync_stage_sf[1]}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|rx_reset_sync_ff[0]}]

# Reference clock constraint - 6.4ns period (156.25 MHz)
create_clock -name {clk_100_p} -period 10.000 [get_ports {clk_100_p}]
create_clock -name gt_refclk -period 6.4 [get_ports {gt_refclk_in_p}]
create_clock -name tx_clk_2x_o [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_tx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div1] -period 3.878
create_clock -name rx_clk_2x_o [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_rx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div1] -period 3.878
create_clock -name tx_clk_o [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_tx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div2] -period 7.756
create_clock -name rx_clk_o [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_rx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div2] -period 7.756
create_generated_clock -name {clk200_inst} -source {clk_100_p} -divide_by 7 -multiply_by 14 -duty_cycle 50.00 { clk200_inst|iopll_0|tennm_pll|outclk[1] }

# Capture clocks into variables (collections)
set sys_clk           [get_clocks -include_generated_clocks clk200_inst]
set rx_clk_2x          [get_clocks -include_generated_clocks rx_clk_2x_o]
set rx_clk_1x         [get_clocks -include_generated_clocks rx_clk_o]
set tx_clk_2x           [get_clocks -include_generated_clocks tx_clk_2x_o]
set tx_clk_1x         [get_clocks -include_generated_clocks tx_clk_o]


set rx_grp [add_to_collection $rx_clk_2x $rx_clk_1x]
set tx_grp [add_to_collection $tx_clk_2x $tx_clk_1x]


create_clock -name {altera_reserved_tck} -period 41.667 [get_ports { altera_reserved_tck }]
set_input_delay -clock altera_reserved_tck 6 [get_ports altera_reserved_tdi]
set_input_delay -clock altera_reserved_tck 6 [get_ports altera_reserved_tms]
set_output_delay -clock altera_reserved_tck -clock_fall -max 6 [get_ports altera_reserved_tdo]


# # Clock groups for asynchronous relationship
set_clock_groups -asynchronous \
    -group [get_clocks gt_refclk] \
    -group $sys_clk \
    -group $rx_grp \
    -group $tx_grp \
    -group [get_clocks clk_100_p] \
    -group [get_clocks {altera_reserved_tck}]


# Multicycle path constraints for synchronous clocks
# Define 2-cycle setup and 1-cycle hold timing between related clock pairs
# RX pair
set_multicycle_path -setup -end   -from $rx_clk_2x    -to $rx_clk_1x  2
set_multicycle_path -hold  -end   -from $rx_clk_2x    -to $rx_clk_1x  1
set_multicycle_path -setup -start -from $rx_clk_1x -to $rx_clk_2x     2
set_multicycle_path -hold  -start -from $rx_clk_1x -to $rx_clk_2x     1

# TX pair
set_multicycle_path -setup -end   -from $tx_clk_2x    -to $tx_clk_1x  2
set_multicycle_path -hold  -end   -from $tx_clk_2x    -to $tx_clk_1x  1
set_multicycle_path -setup -start -from $tx_clk_1x -to $tx_clk_2x     2
set_multicycle_path -hold  -start -from $tx_clk_1x -to $tx_clk_2x     1

set_false_path -to [get_ports {fpga_led[*]}]
set_false_path -to [get_ports {i2c_qsfpdd0_scl}]
set_false_path -to [get_ports {i2c_qsfpdd0_sda}]
#set_false_path -to [get_ports {qsfpdd0_fpga_led[*]}]
#set_false_path -to [get_ports {qsfpdd1_fpga_led[*]}]
#set_false_path -to [get_ports {qsfpdd_12v_port_en}]
#set_false_path -from [get_ports {qsfpdd_1v2_port_int_n}]
