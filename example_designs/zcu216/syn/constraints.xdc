# SPDX-License-Identifier: LicenseRef-LICENSE
# Copyright (c) 2025 Riverlane Ltd.
# Original authors: Dogancan Davutoglu, Aniket Datta, Gargi Sunil

create_clock -period 6.400 -name gt_refclk [get_ports gt_refclk_in_p]
set_property PACKAGE_PIN M34 [get_ports gt_refclk_in_p]

create_generated_clock -name rx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name gt_rx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/RXOUTCLK}]
create_generated_clock -name tx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name gt_tx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]

set_clock_groups -asynchronous -group [get_clocks gt_refclk] -group [get_clocks {rx_clk gt_rx_clk}] -group [get_clocks {tx_clk gt_tx_clk}]
set_property CLOCK_DELAY_GROUP rx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/rx_clk || NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gt_rx_clk}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/tx_clk || NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gt_tx_clk}]

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

set_property PACKAGE_PIN B26 [get_ports {led[0]}]
set_property PACKAGE_PIN E24 [get_ports {led[1]}]
set_property PACKAGE_PIN G26 [get_ports {led[2]}]

set_property IOSTANDARD LVCMOS18 [get_ports {SFP_tx_enable[0]}]
set_property IOSTANDARD LVCMOS18 [get_ports {SFP_tx_enable[1]}]
set_property IOSTANDARD LVCMOS18 [get_ports {SFP_tx_enable[2]}]
set_property IOSTANDARD LVCMOS18 [get_ports {SFP_tx_enable[3]}]

set_property PACKAGE_PIN K16 [get_ports {SFP_tx_enable[0]}]
set_property PACKAGE_PIN K17 [get_ports {SFP_tx_enable[1]}]
set_property PACKAGE_PIN K14 [get_ports {SFP_tx_enable[2]}]
set_property PACKAGE_PIN K15 [get_ports {SFP_tx_enable[3]}]



connect_debug_port u_ila_2/probe4 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_GTY_transceiver.cdr_stable_out]]
connect_debug_port u_ila_2/probe5 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_GTY_transceiver.qpll_lock_out]]








connect_debug_port u_ila_0/probe31 [get_nets [list i_QECIPHY/i_qeciphy_serdes/rx_datapath_aligned_o]]
connect_debug_port u_ila_0/probe33 [get_nets [list i_QECIPHY/i_qeciphy_rx_channeldecoder/rx_rdy_o]]
connect_debug_port u_ila_0/probe36 [get_nets [list i_QECIPHY/i_qeciphy_serdes/rx_word_aligned]]
connect_debug_port u_ila_1/probe1 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/axis_datapath_rst_n_o]]
connect_debug_port u_ila_1/probe2 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/axis_datapath_rst_state]]
connect_debug_port u_ila_1/probe3 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/axis_rst_n_i]]
connect_debug_port u_ila_1/probe6 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/gt_power_good_i]]
connect_debug_port u_ila_1/probe7 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/gt_rst_state]]
connect_debug_port u_ila_1/probe8 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/gt_rx_rst_done_i]]
connect_debug_port u_ila_1/probe9 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/gt_tx_rst_done_i]]
connect_debug_port u_ila_1/probe10 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/in_datapath_delay_state]]
connect_debug_port u_ila_1/probe11 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/in_done_state]]
connect_debug_port u_ila_1/probe12 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/in_gt_delay_state]]
connect_debug_port u_ila_1/probe13 [get_nets [list i_QECIPHY/i_qeciphy_resetcontroller/rst_done_o]]

create_debug_core u_ila_0 ila
set_property ALL_PROBE_SAME_MU true [get_debug_cores u_ila_0]
set_property ALL_PROBE_SAME_MU_CNT 1 [get_debug_cores u_ila_0]
set_property C_ADV_TRIGGER false [get_debug_cores u_ila_0]
set_property C_DATA_DEPTH 4096 [get_debug_cores u_ila_0]
set_property C_EN_STRG_QUAL false [get_debug_cores u_ila_0]
set_property C_INPUT_PIPE_STAGES 0 [get_debug_cores u_ila_0]
set_property C_TRIGIN_EN false [get_debug_cores u_ila_0]
set_property C_TRIGOUT_EN false [get_debug_cores u_ila_0]
set_property port_width 1 [get_debug_ports u_ila_0/clk]
connect_debug_port u_ila_0/clk [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/rx_clk_2x_o]]
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe0]
set_property port_width 32 [get_debug_ports u_ila_0/probe0]
connect_debug_port u_ila_0/probe0 [get_nets [list {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[0]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[1]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[2]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[3]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[4]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[5]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[6]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[7]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[8]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[9]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[10]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[11]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[12]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[13]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[14]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[15]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[16]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[17]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[18]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[19]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[20]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[21]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[22]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[23]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[24]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[25]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[26]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[27]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[28]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[29]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[30]} {i_QECIPHY/i_qeciphy_serdes/rx_tdata_32b[31]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe1]
set_property port_width 4 [get_debug_ports u_ila_0/probe1]
connect_debug_port u_ila_0/probe1 [get_nets [list {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/slot_count[0]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/slot_count[1]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/slot_count[2]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/slot_count[3]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe2]
set_property port_width 7 [get_debug_ports u_ila_0/probe2]
connect_debug_port u_ila_0/probe2 [get_nets [list {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_idle_count[0]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_idle_count[1]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_idle_count[2]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_idle_count[3]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_idle_count[4]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_idle_count[5]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_idle_count[6]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe3]
set_property port_width 8 [get_debug_ports u_ila_0/probe3]
connect_debug_port u_ila_0/probe3 [get_nets [list {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_count[0]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_count[1]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_count[2]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_count[3]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_count[4]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_count[5]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_count[6]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_slide_count[7]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe4]
set_property port_width 3 [get_debug_ports u_ila_0/probe4]
connect_debug_port u_ila_0/probe4 [get_nets [list {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/fsm[0]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/fsm[1]} {i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/fsm[2]}]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe5]
set_property port_width 1 [get_debug_ports u_ila_0/probe5]
connect_debug_port u_ila_0/probe5 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/crc_1_slot]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe6]
set_property port_width 1 [get_debug_ports u_ila_0/probe6]
connect_debug_port u_ila_0/probe6 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/crc_2_slot]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe7]
set_property port_width 1 [get_debug_ports u_ila_0/probe7]
connect_debug_port u_ila_0/probe7 [get_nets [list i_QECIPHY/i_qeciphy_rx_channeldecoder/i_rx_monitor/crc_error_o]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe8]
set_property port_width 1 [get_debug_ports u_ila_0/probe8]
connect_debug_port u_ila_0/probe8 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/data_slot]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe9]
set_property port_width 1 [get_debug_ports u_ila_0/probe9]
connect_debug_port u_ila_0/probe9 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/faw_1_slot]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe10]
set_property port_width 1 [get_debug_ports u_ila_0/probe10]
connect_debug_port u_ila_0/probe10 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/faw_2_slot]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe11]
set_property port_width 1 [get_debug_ports u_ila_0/probe11]
connect_debug_port u_ila_0/probe11 [get_nets [list i_QECIPHY/i_qeciphy_rx_channeldecoder/i_qeciphy_rx_boundary_gen/faw_boundary_en]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe12]
set_property port_width 1 [get_debug_ports u_ila_0/probe12]
connect_debug_port u_ila_0/probe12 [get_nets [list i_QECIPHY/i_qeciphy_rx_channeldecoder/i_rx_monitor/faw_error_o]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe13]
set_property port_width 1 [get_debug_ports u_ila_0/probe13]
connect_debug_port u_ila_0/probe13 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_GTY_transceiver.rxpmaresetdone]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe14]
set_property port_width 1 [get_debug_ports u_ila_0/probe14]
connect_debug_port u_ila_0/probe14 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gt_rx_rst_done]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe15]
set_property port_width 1 [get_debug_ports u_ila_0/probe15]
connect_debug_port u_ila_0/probe15 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gt_rx_rst_done_o]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe16]
set_property port_width 1 [get_debug_ports u_ila_0/probe16]
connect_debug_port u_ila_0/probe16 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_align_boundary_check]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe17]
set_property port_width 1 [get_debug_ports u_ila_0/probe17]
connect_debug_port u_ila_0/probe17 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_align_boundary_check_fail]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe18]
set_property port_width 1 [get_debug_ports u_ila_0/probe18]
connect_debug_port u_ila_0/probe18 [get_nets [list i_QECIPHY/i_qeciphy_serdes/rx_byte_aligned]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe19]
set_property port_width 1 [get_debug_ports u_ila_0/probe19]
connect_debug_port u_ila_0/probe19 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_rx_bytealigner/rx_datan_comma_m]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe20]
set_property port_width 1 [get_debug_ports u_ila_0/probe20]
connect_debug_port u_ila_0/probe20 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/rx_pma_rst_done_internal]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe21]
set_property port_width 1 [get_debug_ports u_ila_0/probe21]
connect_debug_port u_ila_0/probe21 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/rx_slide_i]]
create_debug_port u_ila_0 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_0/probe22]
set_property port_width 1 [get_debug_ports u_ila_0/probe22]
connect_debug_port u_ila_0/probe22 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/rx_slide_rdy_o]]
create_debug_core u_ila_1 ila
set_property ALL_PROBE_SAME_MU true [get_debug_cores u_ila_1]
set_property ALL_PROBE_SAME_MU_CNT 1 [get_debug_cores u_ila_1]
set_property C_ADV_TRIGGER false [get_debug_cores u_ila_1]
set_property C_DATA_DEPTH 4096 [get_debug_cores u_ila_1]
set_property C_EN_STRG_QUAL false [get_debug_cores u_ila_1]
set_property C_INPUT_PIPE_STAGES 0 [get_debug_cores u_ila_1]
set_property C_TRIGIN_EN false [get_debug_cores u_ila_1]
set_property C_TRIGOUT_EN false [get_debug_cores u_ila_1]
set_property port_width 1 [get_debug_ports u_ila_1/clk]
connect_debug_port u_ila_1/clk [get_nets [list FCLK]]
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_1/probe0]
set_property port_width 7 [get_debug_ports u_ila_1/probe0]
connect_debug_port u_ila_1/probe0 [get_nets [list {i_QECIPHY/i_qeciphy_resetcontroller/state[0]} {i_QECIPHY/i_qeciphy_resetcontroller/state[1]} {i_QECIPHY/i_qeciphy_resetcontroller/state[2]} {i_QECIPHY/i_qeciphy_resetcontroller/state[3]} {i_QECIPHY/i_qeciphy_resetcontroller/state[4]} {i_QECIPHY/i_qeciphy_resetcontroller/state[5]} {i_QECIPHY/i_qeciphy_resetcontroller/state[6]}]]
create_debug_port u_ila_1 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_1/probe1]
set_property port_width 1 [get_debug_ports u_ila_1/probe1]
connect_debug_port u_ila_1/probe1 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_GTY_transceiver.cdr_stable]]
create_debug_port u_ila_1 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_1/probe2]
set_property port_width 1 [get_debug_ports u_ila_1/probe2]
connect_debug_port u_ila_1/probe2 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_GTY_transceiver.qpll0_lock]]
create_debug_core u_ila_2 ila
set_property ALL_PROBE_SAME_MU true [get_debug_cores u_ila_2]
set_property ALL_PROBE_SAME_MU_CNT 1 [get_debug_cores u_ila_2]
set_property C_ADV_TRIGGER false [get_debug_cores u_ila_2]
set_property C_DATA_DEPTH 4096 [get_debug_cores u_ila_2]
set_property C_EN_STRG_QUAL false [get_debug_cores u_ila_2]
set_property C_INPUT_PIPE_STAGES 0 [get_debug_cores u_ila_2]
set_property C_TRIGIN_EN false [get_debug_cores u_ila_2]
set_property C_TRIGOUT_EN false [get_debug_cores u_ila_2]
set_property port_width 1 [get_debug_ports u_ila_2/clk]
connect_debug_port u_ila_2/clk [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/tx_clk_2x_o]]
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_2/probe0]
set_property port_width 1 [get_debug_ports u_ila_2/probe0]
connect_debug_port u_ila_2/probe0 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_GTY_transceiver.tx_rx_active]]
create_debug_port u_ila_2 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_2/probe1]
set_property port_width 1 [get_debug_ports u_ila_2/probe1]
connect_debug_port u_ila_2/probe1 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_GTY_transceiver.txpmaresetdone]]
create_debug_port u_ila_2 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_2/probe2]
set_property port_width 1 [get_debug_ports u_ila_2/probe2]
connect_debug_port u_ila_2/probe2 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gt_power_good_o]]
create_debug_port u_ila_2 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_2/probe3]
set_property port_width 1 [get_debug_ports u_ila_2/probe3]
connect_debug_port u_ila_2/probe3 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gt_tx_rst_done]]
create_debug_port u_ila_2 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_2/probe4]
set_property port_width 1 [get_debug_ports u_ila_2/probe4]
connect_debug_port u_ila_2/probe4 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gt_tx_rst_done_o]]
create_debug_port u_ila_2 probe
set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports u_ila_2/probe5]
set_property port_width 1 [get_debug_ports u_ila_2/probe5]
connect_debug_port u_ila_2/probe5 [get_nets [list i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/tx_pma_rst_done_internal]]
set_property C_CLK_INPUT_FREQ_HZ 300000000 [get_debug_cores dbg_hub]
set_property C_ENABLE_CLK_DIVIDER false [get_debug_cores dbg_hub]
set_property C_USER_SCAN_CHAIN 1 [get_debug_cores dbg_hub]
connect_debug_port dbg_hub/clk [get_nets FCLK]
