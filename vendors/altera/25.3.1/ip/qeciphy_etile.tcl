package require -exact qsys 25.3.1

# --- Parameters: overridden by $argv when called from quartus_ip.tcl ---
set device         "AGFB014R24B2E2V"
set device_family  "Agilex 7"
set line_rate_mbps 10312.5
set rclk_freq_mhz  156.25

if {[llength $argv] >= 1} { set device         [lindex $argv 0] }
if {[llength $argv] >= 2} { set device_family  [lindex $argv 1] }
if {[llength $argv] >= 3} { set line_rate_mbps [lindex $argv 2] }
if {[llength $argv] >= 4} { set rclk_freq_mhz  [lindex $argv 3] }

# create the system "qeciphy_etile"
proc do_create_qeciphy_etile {} {
	global device device_family line_rate_mbps rclk_freq_mhz
	# create the system
	create_system qeciphy_etile
	set_project_property BOARD {default}
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $device_family
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance xcvrnphy_fme_0 xcvrnphy_fme 4.1.2
	set_instance_parameter_value xcvrnphy_fme_0 {DR_NRZ_PAM4} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_multi_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_recipe_cnt} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_recipe_data0} {}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_recipe_data1} {}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_recipe_data2} {}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_recipe_data3} {}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_recipe_data4} {}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_recipe_data5} {}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_recipe_data6} {}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_recipe_data7} {}
	set_instance_parameter_value xcvrnphy_fme_0 {adpt_recipe_select} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {aggregate_rsfec_enable_checkbox} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {cal_recipe_sel} {NRZ_28Gbps_VSR}
	set_instance_parameter_value xcvrnphy_fme_0 {channels} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {cr3_advanced_aib_settings_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_gs1_val_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_gs1_val_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_gs2_val_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_gs2_val_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_hf_max_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_hf_max_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_hf_min_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_hf_min_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_hf_val_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_hf_val_ada_a} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_hf_val_ada_b} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_hf_val_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_lf_max_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_lf_max_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_lf_min_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_lf_min_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_lf_val_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_lf_val_ada_a} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_lf_val_ada_b} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {ctle_lf_val_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {design_environment} {NATIVE}
	set_instance_parameter_value xcvrnphy_fme_0 {design_example_filename} {top}
	set_instance_parameter_value xcvrnphy_fme_0 {deskew_pma_only_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {dr_25g_cpri_nphy} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {duplex_mode} {duplex}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_am_encoding40g_0} {9467463}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_am_encoding40g_1} {15779046}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_am_encoding40g_2} {12936603}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_am_encoding40g_3} {10647869}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_check_random_idles} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_disable_link_fault_rf} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_ehip_dist_clk_sel} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_ehip_mode} {ehip_disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_ehip_rate} {rate_100gx4}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_enable_rx_stats_snapshot} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_enable_tx_stats_snapshot} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_enforce_max_frame_size} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_fec_dist_clk_sel} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_flow_control} {none}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_flow_control_holdoff_mode} {per_queue}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_force_deskew_done} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_force_hip_ready} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_force_link_fault_rf} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_forward_rx_pause_requests} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_func_mode} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_hi_ber_monitor} {enable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_holdoff_quanta} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_ipg_removed_per_am_period} {20}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_is_usr_avmm} {false}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_keep_rx_crc} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_link_fault_mode} {lf_off}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pause_quanta} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_holdoff_quanta_0} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_holdoff_quanta_1} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_holdoff_quanta_2} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_holdoff_quanta_3} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_holdoff_quanta_4} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_holdoff_quanta_5} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_holdoff_quanta_6} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_holdoff_quanta_7} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_pause_quanta_0} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_pause_quanta_1} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_pause_quanta_2} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_pause_quanta_3} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_pause_quanta_4} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_pause_quanta_5} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_pause_quanta_6} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_pfc_pause_quanta_7} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_powerdown_mode} {powerup}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_ptp_timestamp_format} {v2}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_ptp_tx_timestamp_method} {ptp_1step}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_remove_pads} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_reset_rx_stats_parity_error} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_reset_tx_stats_parity_error} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rx_aib_dp_latency} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rx_clock_period} {162689}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rx_length_checking} {enable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rx_max_frame_size} {1518}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rx_pause_daddr} {1652522221569}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rx_pcs_max_skew} {47}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rx_preamble_passthrough} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rx_ptp_dp_latency} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rx_ptp_extra_latency} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rx_vlan_detection} {enable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_rxcrc_covers_preamble} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_sim_mode} {enable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_source_address_insertion} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_strict_preamble_checking} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_strict_sfd_checking} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_aib_dp_latency} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_clock_period} {162689}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_ipg_size} {ipg_12}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_mac_data_flow} {enable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_max_frame_size} {1518}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_pause_daddr} {1652522221569}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_pause_saddr} {247393538562781}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_pld_fifo_almost_full_level} {16}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_preamble_passthrough} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_ptp_asym_latency} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_ptp_dp_latency} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_ptp_extra_latency} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_tx_vlan_detection} {enable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_txcrc_covers_preamble} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_txmac_saddr} {73588229205}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_uniform_holdoff_quanta} {65535}
	set_instance_parameter_value xcvrnphy_fme_0 {elane_use_factory_settings} {true}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_advanced_options} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_custom_backplane_mode_checkbox} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_debug_options} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_direct_reset_control} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_ehip_options} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_ind_channel} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_ind_txrx} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_infuture_options} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_inprogress_options} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_interlaken_options} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_latency_measurement_feature} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_low_rate_pam4} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_manual_reset} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_pma_reset} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_latency_measurement} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_pll_refclk} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_pma_initialized} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_clkout2} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_clkout2_hioint} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_clkout_hioint} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_enh_pmaif_fifo_overflow} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_fifo_empty} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_fifo_full} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_fifo_pempty} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_fifo_pfull} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_fifo_rd_en} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_is_lockedtodata} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_pcs_fifo_empty} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_pcs_fifo_full} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_pma_clkslip} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_pma_elecidle} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_pma_en} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_pmaif_bitslip} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_rx_pmaif_fifo_underflow} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_clkin2} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_clkout2} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_clkout2_hioint} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_clkout_hioint} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_dll_lock} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_enh_pmaif_fifo_almost_empty} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_enh_pmaif_fifo_almost_full} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_enh_pmaif_fifo_overflow} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_enh_pmaif_fifo_underflow} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_fifo_empty} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_fifo_full} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_fifo_pempty} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_fifo_pfull} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_pcs_fifo_empty} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_pcs_fifo_full} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_pma_en} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_port_tx_pmaif_bitslip} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_ptp_measurement_feature} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_ptp_measurement_port} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_rsfec_fc_cpri_options_checkbox} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_rsfec_support_mode_options_checkbox} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_seq} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_simple_interface} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_spico_reset} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_split_interface} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {enable_workaround_rules} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {internal_derived_parameter_select} {l_is_loopback_mode_enabled}
	set_instance_parameter_value xcvrnphy_fme_0 {l_enable_reset_controller} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_adapt_rx_rx_10g_krfec_rx_diag_data_status_polling_bypass} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_adapt_rx_rx_pld_8g_wa_boundary_polling_bypass} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_adapt_rx_rx_pld_pma_pcie_sw_done_polling_bypass} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_adapt_rx_rx_pld_pma_reser_in_polling_bypass} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_adapt_rx_rx_pld_pma_testbus_polling_bypass} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_adapt_rx_rx_pld_test_data_polling_bypass} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_adapt_tx_dv_gating} {disable}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_clocking_mode} {fec_dir_adp_clk_0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_am_5bad_dis0} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_am_5bad_dis1} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_am_5bad_dis2} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_am_5bad_dis3} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_blk_chk_dis0} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_blk_chk_dis1} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_blk_chk_dis2} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_blk_chk_dis3} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_enter_align_entry_field} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_exit_align_entry_field} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_fec_3bad_dis0} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_fec_3bad_dis1} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_fec_3bad_dis2} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_fec_3bad_dis3} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_sf_dis0} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_sf_dis1} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_sf_dis2} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_sf_dis3} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_swaps0} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_swaps1} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_swaps2} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_swaps3} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_test} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_trans_byp0_string} {Enabled}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_trans_byp1_string} {Enabled}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_trans_byp2_string} {Enabled}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_eng_trans_byp3_string} {Enabled}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_fibre_channel0_string} {Basic Mode}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_fibre_channel1_string} {Basic Mode}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_fibre_channel2_string} {Basic Mode}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_fibre_channel3_string} {Basic Mode}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_indic_byp0} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_indic_byp1} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_indic_byp2} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_core_indic_byp3} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_deskew_channels_clear} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_fec_tx2rx_loopback0} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_fec_tx2rx_loopback1} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_fec_tx2rx_loopback2} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_fec_tx2rx_loopback3} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_first_lane_sel} {first_lane0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_force_deskew_done} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_force_fec_ready} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_source_lane_ena0} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_source_lane_ena1} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_source_lane_ena2} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_source_lane_ena3} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_tx_data_source_sel0} {fec_tx_lane_off0}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_tx_data_source_sel1} {fec_tx_lane_off1}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_tx_data_source_sel2} {fec_tx_lane_off2}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfec_tx_data_source_sel3} {fec_tx_lane_off3}
	set_instance_parameter_value xcvrnphy_fme_0 {l_hssi_rsfecrx_mux_rx_data_source} {fec_rx_data}
	set_instance_parameter_value xcvrnphy_fme_0 {loopback_tx_clk_sel} {internal_clk}
	set_instance_parameter_value xcvrnphy_fme_0 {message_level} {error}
	set_instance_parameter_value xcvrnphy_fme_0 {parallel_lpbk_mode} {disabled}
	set_instance_parameter_value xcvrnphy_fme_0 {pcs_manual_rx_fifo_rd_clk_sel_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pcs_rx_fifo_rd_clk_sel} {tx_pma_clk}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_debug_ports_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_manual_transfer_clk_mode_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_osc_clk_divider} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_rx_clkout2_sel} {half-rate}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_rx_clkout_sel} {half-rate}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_rx_coreclkin_clock_network} {dedicated}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_rx_double_width_transfer_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_rx_fast_pipeln_reg_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_rx_fifo_mode} {phase_comp}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_rx_fifo_pempty_thld} {2}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_rx_fifo_pfull_thld} {10}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_rx_manual_mode_transfer_clk_hz} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_clkout2_sel} {half-rate}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_clkout_sel} {half-rate}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_coreclkin2_clock_network} {dedicated}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_coreclkin2_external_clk_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_coreclkin_clock_network} {dedicated}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_double_width_transfer_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_fast_pipeln_reg_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_fifo_mode} {phase_comp}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_fifo_pempty_thld} {2}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_fifo_pfull_thld} {10}
	set_instance_parameter_value xcvrnphy_fme_0 {pldif_tx_manual_mode_transfer_clk_hz} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pll_outclk_freq_mhz} {400}
	set_instance_parameter_value xcvrnphy_fme_0 {pll_refclk_cnt} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pll_refclk_freq_mhz} {250.000000}
	set_instance_parameter_value xcvrnphy_fme_0 {pll_select} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_an_constraints_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_disable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_example_qsf_strings} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_ical_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_ical_poweron_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_plls} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_rx_clkdiv66_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_rx_clkfullrate_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_rx_clkhalfrate_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_rx_data_rate} $line_rate_mbps
	set_instance_parameter_value xcvrnphy_fme_0 {pma_rx_dedicated_refclk_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_rx_dedicated_refclk_select} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_rx_modulation} {NRZ}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_rx_pll_post_divider} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_rx_pll_refclk_freq_mhz} {156.250000}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_seq_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_bonding_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_clkdiv66_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_data_rate} $line_rate_mbps
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_atten_tap} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_main_tap} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_post1_tap} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_post_tap} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_powerup_disable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_pre1_tap} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_pre2_tap} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_pre3_tap} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_pre_tap} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_slew_rate} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_eq_vod} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_modulation} {NRZ}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_pll_post_divider} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_pll_refclk_freq_mhz} {156.250000}
	set_instance_parameter_value xcvrnphy_fme_0 {pma_tx_pll_select} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_bit_interleaving_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_fifo_aempty_thld} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_fifo_afull_thld} {20}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_fifo_empty_thld} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_fifo_full_thld} {31}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_fifo_rd_empty_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_fifo_wr_clk_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_fifo_wr_full_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_gb_bit_reversal_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_gb_bitslip_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_gb_mode} {rx_gb_64_64}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_gb_sh_bit_mode} {bit1-bit0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_gb_sh_bit_reversal_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_gb_width_adapt_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_gb_word_order} {lower}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_soft_reset_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_rx_width} {20}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_bit_interleaving_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_fifo_aempty_thld} {7}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_fifo_afull_thld} {20}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_fifo_empty_thld} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_fifo_full_thld} {31}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_fifo_mode} {phase_comp}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_fifo_rd_empty_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_fifo_wr_full_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_gb_bit_reversal_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_gb_bitslip_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_gb_mode} {tx_gb_64_64}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_gb_sh_bit_mode} {bit1-bit0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_gb_sh_bit_reversal_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_gb_width_adapt_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_gb_word_order} {lower}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_soft_reset_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_to_rx_parallel_loopback_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {pmaif_tx_width} {20}
	set_instance_parameter_value xcvrnphy_fme_0 {protocol_mode} {pma_direct}
	set_instance_parameter_value xcvrnphy_fme_0 {ptp_data_channels} {4}
	set_instance_parameter_value xcvrnphy_fme_0 {ptp_ethernet_data_rsfec_enabled} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_debug} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_enable_avmm_busy_port} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_file_prefix} {altera_xcvr_rcfg_10}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_files_as_common_package} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_h_file_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_iface_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_jtag_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_mif_file_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_multi_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_profile_cnt} {2}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_profile_data0} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_profile_data1} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_profile_data2} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_profile_data3} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_profile_data4} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_profile_data5} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_profile_data6} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_profile_data7} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_profile_select} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_reduced_files_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_sdc_derived_profile_data0} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_sdc_derived_profile_data1} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_sdc_derived_profile_data2} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_sdc_derived_profile_data3} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_sdc_derived_profile_data4} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_sdc_derived_profile_data5} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_sdc_derived_profile_data6} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_sdc_derived_profile_data7} {}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_separate_avmm_busy} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_shared} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_sv_file_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcfg_txt_file_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rcp_load_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {reduced_reset_sim_time} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {reduced_sim_time} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {reset_separation_ns} {200}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_a_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_a_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_b0_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_b0_ada_a} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_b0_ada_b} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_b0_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_b0t_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_b0t_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_b1_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_b1_ada_a} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_b1_ada_b} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_b1_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p0_val_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p0_val_ada_a} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p0_val_ada_b} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p0_val_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p1_max_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p1_max_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p1_min_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p1_min_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p1_val_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p1_val_ada_a} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p1_val_ada_b} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p1_val_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p2_max_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p2_max_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p2_min_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p2_min_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p2_val_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p2_val_ada_a} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p2_val_ada_b} {adaptable}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_p2_val_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_reserved0_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_reserved0_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_reserved1_a} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rf_reserved1_b} {999}
	set_instance_parameter_value xcvrnphy_fme_0 {rsfec_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rx_bit_counter_rollover} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {rx_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {rx_nd_maib_op_mode} {rx_dll_enable}
	set_instance_parameter_value xcvrnphy_fme_0 {set_capability_reg_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {set_csr_soft_logic_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {set_embedded_debug_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {set_op_mode_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {set_rcfg_emb_strm_enable} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {set_user_identifier} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {space_ns} {100}
	set_instance_parameter_value xcvrnphy_fme_0 {support_mode} {user_mode}
	set_instance_parameter_value xcvrnphy_fme_0 {support_mode_hssi_adpt} {user_mode}
	set_instance_parameter_value xcvrnphy_fme_0 {support_mode_pld_adpt} {user_mode}
	set_instance_parameter_value xcvrnphy_fme_0 {support_mode_rsfec} {advanced_user_mode}
	set_instance_parameter_value xcvrnphy_fme_0 {suppress_design_example_messages} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {t_rx_reset} {100}
	set_instance_parameter_value xcvrnphy_fme_0 {t_tx_reset} {100}
	set_instance_parameter_value xcvrnphy_fme_0 {tx_enable} {1}
	set_instance_parameter_value xcvrnphy_fme_0 {tx_nd_maib_op_mode} {tx_dcc_enable}
	set_instance_parameter_value xcvrnphy_fme_0 {user_bti_channel_clock_select} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {user_bti_channel_ref_clock_freq_mhz} {100}
	set_instance_parameter_value xcvrnphy_fme_0 {user_enable_serialliteiv} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {user_preserve_unused_xcvr_channels} {0}
	set_instance_parameter_value xcvrnphy_fme_0 {user_set_int_seq_serd_en} {seq_en_all}
	set_instance_parameter_value xcvrnphy_fme_0 {user_set_serdes_en_seq} {en_serdes_seq}
	set_instance_parameter_value xcvrnphy_fme_0 {validation_rule_select} {}
	set_instance_property xcvrnphy_fme_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property reset EXPORT_OF xcvrnphy_fme_0.reset
	set_interface_property tx_ready EXPORT_OF xcvrnphy_fme_0.tx_ready
	set_interface_property rx_ready EXPORT_OF xcvrnphy_fme_0.rx_ready
	set_interface_property tx_pma_ready EXPORT_OF xcvrnphy_fme_0.tx_pma_ready
	set_interface_property rx_pma_ready EXPORT_OF xcvrnphy_fme_0.rx_pma_ready
	set_interface_property tx_serial_data EXPORT_OF xcvrnphy_fme_0.tx_serial_data
	set_interface_property tx_serial_data_n EXPORT_OF xcvrnphy_fme_0.tx_serial_data_n
	set_interface_property rx_serial_data EXPORT_OF xcvrnphy_fme_0.rx_serial_data
	set_interface_property rx_serial_data_n EXPORT_OF xcvrnphy_fme_0.rx_serial_data_n
	set_interface_property pll_refclk0 EXPORT_OF xcvrnphy_fme_0.pll_refclk0
	set_interface_property rx_is_lockedtodata EXPORT_OF xcvrnphy_fme_0.rx_is_lockedtodata
	set_interface_property tx_parallel_data EXPORT_OF xcvrnphy_fme_0.tx_parallel_data
	set_interface_property rx_parallel_data EXPORT_OF xcvrnphy_fme_0.rx_parallel_data
	set_interface_property tx_coreclkin EXPORT_OF xcvrnphy_fme_0.tx_coreclkin
	set_interface_property rx_coreclkin EXPORT_OF xcvrnphy_fme_0.rx_coreclkin
	set_interface_property tx_clkout EXPORT_OF xcvrnphy_fme_0.tx_clkout
	set_interface_property tx_clkout2 EXPORT_OF xcvrnphy_fme_0.tx_clkout2
	set_interface_property rx_clkout EXPORT_OF xcvrnphy_fme_0.rx_clkout
	set_interface_property rx_clkout2 EXPORT_OF xcvrnphy_fme_0.rx_clkout2

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="xcvrnphy_fme_0">
  <datum __value="_sortIndex" value="0" type="int" />
 </element>
</bonusData>
}
	set_module_property FILE {qeciphy_etile.ip}
	set_module_property GENERATION_ID {0x00000000}
	set_module_property NAME {qeciphy_etile}

	# save the system
	sync_sysinfo_parameters
	save_system qeciphy_etile
}

proc do_set_exported_interface_sysinfo_parameters {} {
}

# create all the systems, from bottom up
do_create_qeciphy_etile

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
