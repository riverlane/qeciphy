package require -exact qsys 25.3.1

# --- Parameters: overridden by $argv when called from quartus_ip.tcl ---
set device         "AGIB027R31B1E1V"
set device_family  "Agilex 7"
set line_rate_mbps 12500
set rclk_freq_mhz  156.25

if {[llength $argv] >= 1} { set device         [lindex $argv 0] }
if {[llength $argv] >= 2} { set device_family  [lindex $argv 1] }
if {[llength $argv] >= 3} { set line_rate_mbps [lindex $argv 2] }
if {[llength $argv] >= 4} { set rclk_freq_mhz  [lindex $argv 3] }

# create the system "qeciphy_ftile"
proc do_create_qeciphy_ftile {} {
	global device device_family line_rate_mbps rclk_freq_mhz
	# create the system
	create_system qeciphy_ftile
	set_project_property BOARD {default}
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $device_family
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance directphy_f_0 directphy_f 4.10.5
	set_instance_parameter_value directphy_f_0 {CLOCK_SELECTION} {0}
	set_instance_parameter_value directphy_f_0 {CLOCK_SELECTION_Board} {3}
	set_instance_parameter_value directphy_f_0 {ENABLE_ANLT} {0}
	set_instance_parameter_value directphy_f_0 {MODE_1000_BASE_KX} {0}
	set_instance_parameter_value directphy_f_0 {avmm1_aib_enable} {0}
	set_instance_parameter_value directphy_f_0 {avmm1_jtag_enable} {0}
	set_instance_parameter_value directphy_f_0 {avmm1_readdv_enable} {0}
	set_instance_parameter_value directphy_f_0 {avmm1_soft_csr_enable} {0}
	set_instance_parameter_value directphy_f_0 {avmm1_split} {0}
	set_instance_parameter_value directphy_f_0 {avmm2_enable} {0}
	set_instance_parameter_value directphy_f_0 {avmm2_jtag_enable} {0}
	set_instance_parameter_value directphy_f_0 {avmm2_readdv_enable} {0}
	set_instance_parameter_value directphy_f_0 {avmm2_split} {0}
	set_instance_parameter_value directphy_f_0 {bk_alt_pam4_grey_code} {0}
	set_instance_parameter_value directphy_f_0 {bk_cfg_kvcc_vreg_offset_en_val} {CFG_KVCC_VREG_OFFSET_EN_VAL_DISABLE}
	set_instance_parameter_value directphy_f_0 {bk_dl_enable} {DETLAT_DIS}
	set_instance_parameter_value directphy_f_0 {bk_en_rxdat_profile} {RXDAT_PROF_EN}
	set_instance_parameter_value directphy_f_0 {bk_ext_ac_cap} {EXTERNAL_AC_CAP_ENABLE}
	set_instance_parameter_value directphy_f_0 {bk_loopback_mode} {SERIAL_EXT_LOOPBACK}
	set_instance_parameter_value directphy_f_0 {bk_pll_pcs3334_ratio} {DIV_33_BY_2}
	set_instance_parameter_value directphy_f_0 {bk_pll_rx_pcs3334_ratio} {RX_DIV_33_BY_2}
	set_instance_parameter_value directphy_f_0 {bk_refclk_source_lane_pll} {PLL_156_MHZ}
	set_instance_parameter_value directphy_f_0 {bk_rx_invert_p_and_n} {RX_INVERT_PN_DIS}
	set_instance_parameter_value directphy_f_0 {bk_rx_lat_bit_for_async} {0}
	set_instance_parameter_value directphy_f_0 {bk_rx_pmadir_frame_len} {5280}
	set_instance_parameter_value directphy_f_0 {bk_rx_precode_en} {0}
	set_instance_parameter_value directphy_f_0 {bk_rx_termination} {RXTERM_OFFSET_P0}
	set_instance_parameter_value directphy_f_0 {bk_rx_user_clk1_en} {0}
	set_instance_parameter_value directphy_f_0 {bk_rx_user_clk1_sel} {0}
	set_instance_parameter_value directphy_f_0 {bk_rx_user_clk2_en} {0}
	set_instance_parameter_value directphy_f_0 {bk_rx_user_clk2_sel} {0}
	set_instance_parameter_value directphy_f_0 {bk_rxdat_1cnt_thld_high} {550000}
	set_instance_parameter_value directphy_f_0 {bk_rxdat_1cnt_thld_low} {450000}
	set_instance_parameter_value directphy_f_0 {bk_sup_mode} {USER_MODE}
	set_instance_parameter_value directphy_f_0 {bk_tx_invert_p_and_n} {TX_INVERT_PN_DIS}
	set_instance_parameter_value directphy_f_0 {bk_tx_precode_en} {0}
	set_instance_parameter_value directphy_f_0 {bk_tx_predivider_en} {0}
	set_instance_parameter_value directphy_f_0 {bk_tx_termination} {TXTERM_OFFSET_P0}
	set_instance_parameter_value directphy_f_0 {bk_tx_user_clk1_en} {0}
	set_instance_parameter_value directphy_f_0 {bk_tx_user_clk1_sel} {0}
	set_instance_parameter_value directphy_f_0 {bk_tx_user_clk2_en} {0}
	set_instance_parameter_value directphy_f_0 {bk_tx_user_clk2_sel} {0}
	set_instance_parameter_value directphy_f_0 {bk_txeq_main_tap} {41.5}
	set_instance_parameter_value directphy_f_0 {bk_txeq_post_tap_1} {0.0}
	set_instance_parameter_value directphy_f_0 {bk_txeq_post_tap_2} {0.0}
	set_instance_parameter_value directphy_f_0 {bk_txeq_post_tap_3} {0.0}
	set_instance_parameter_value directphy_f_0 {bk_txeq_post_tap_4} {0.0}
	set_instance_parameter_value directphy_f_0 {bk_txeq_pre_tap_1} {0.0}
	set_instance_parameter_value directphy_f_0 {bk_txeq_pre_tap_2} {0.0}
	set_instance_parameter_value directphy_f_0 {bk_txeq_pre_tap_3} {0.0}
	set_instance_parameter_value directphy_f_0 {bk_txout_tristate_en} {TXOUT_TRISTATE_DIS}
	set_instance_parameter_value directphy_f_0 {clocking_mode} {xcvr}
	set_instance_parameter_value directphy_f_0 {design_environment} {NATIVE}
	set_instance_parameter_value directphy_f_0 {dp_mode} {0}
	set_instance_parameter_value directphy_f_0 {duplex_mode} {duplex}
	set_instance_parameter_value directphy_f_0 {dv_cwbin_timeout} {0}
	set_instance_parameter_value directphy_f_0 {ed_ack} {0}
	set_instance_parameter_value directphy_f_0 {ed_board} {None}
	set_instance_parameter_value directphy_f_0 {ed_hdl_sel} {Verilog}
	set_instance_parameter_value directphy_f_0 {ed_sel} {None}
	set_instance_parameter_value directphy_f_0 {enable_N_width_ready_signal} {0}
	set_instance_parameter_value directphy_f_0 {enable_advanced_options} {0}
	set_instance_parameter_value directphy_f_0 {enable_cwbin_gui} {0}
	set_instance_parameter_value directphy_f_0 {enable_fgt_rx_cdr_fast_freeze_sel} {0}
	set_instance_parameter_value directphy_f_0 {enable_fgt_rx_cdr_set_locktoref} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_Rx_pstate_lx} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_Rx_term_hiz_en_lx_a} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_Tx_pstate_lx} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_rx_cdr_divclk_link0} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_rx_cdr_divclk_link1} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_rx_cdr_freeze} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_rx_set_locktodata} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_rx_set_locktoref} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_rx_signal_detect} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_rx_signal_detect_lfps} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_rx_status} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_tx_beacon} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_tx_status} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_txdetectrx_ack} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_txdetectrx_req} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_fgt_txdetectrx_stat} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_latency_measurement} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_clkout2} {1}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_clkout2_hioint} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_clkout_hioint} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_fifo_empty} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_fifo_full} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_fifo_pempty} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_fifo_pfull} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_fifo_rd_en} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_pcs_fifo_empty} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_pcs_fifo_full} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_pmaif_fifo_empty} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_pmaif_fifo_pempty} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_rx_pmaif_fifo_pfull} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_cadence_slow_clk_locked} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_clkout2} {1}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_clkout2_hioint} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_clkout_hioint} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_dll_lock} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_fifo_empty} {1}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_fifo_full} {1}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_fifo_pempty} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_fifo_pfull} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_pcs_fifo_empty} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_pcs_fifo_full} {0}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_pmaif_fifo_empty} {1}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_pmaif_fifo_pempty} {1}
	set_instance_parameter_value directphy_f_0 {enable_port_tx_pmaif_fifo_pfull} {1}
	set_instance_parameter_value directphy_f_0 {enable_simple_interface} {0}
	set_instance_parameter_value directphy_f_0 {enable_split_interface} {0}
	set_instance_parameter_value directphy_f_0 {enable_tx_ssc_interface} {0}
	set_instance_parameter_value directphy_f_0 {enable_user_fec_lock} {0}
	set_instance_parameter_value directphy_f_0 {fec_802p3ck} {0}
	set_instance_parameter_value directphy_f_0 {fec_en} {0}
	set_instance_parameter_value directphy_f_0 {fec_lpbk_en} {0}
	set_instance_parameter_value directphy_f_0 {fgt_core_pll_enable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_protocol_mode} {DISABLED}
	set_instance_parameter_value directphy_f_0 {fgt_rx_cdr_divclk_link0_sel} {0}
	set_instance_parameter_value directphy_f_0 {fgt_rx_cdr_divclk_link1_sel} {0}
	set_instance_parameter_value directphy_f_0 {fgt_rx_cdr_lock_mode} {auto}
	set_instance_parameter_value directphy_f_0 {fgt_rx_cdr_rxuserclk_div} {100}
	set_instance_parameter_value directphy_f_0 {fgt_rx_cdr_rxuserclk_enable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_rx_pll_bw_sel} {LOW}
	set_instance_parameter_value directphy_f_0 {fgt_rx_pll_l_cnt} {1}
	set_instance_parameter_value directphy_f_0 {fgt_rx_pll_m_cnt} {1}
	set_instance_parameter_value directphy_f_0 {fgt_rx_pll_manual_enable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_rx_pll_n_cnt} {1}
	set_instance_parameter_value directphy_f_0 {fgt_rx_pll_refclk_freq_mhz} $rclk_freq_mhz
	set_instance_parameter_value directphy_f_0 {fgt_rx_sata_squelch_det_enable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_rx_serdes_adapt_mode} {auto}
	set_instance_parameter_value directphy_f_0 {fgt_rx_serdes_gray_coding_enable} {1}
	set_instance_parameter_value directphy_f_0 {fgt_rx_serdes_prbs_mon_mode} {disable}
	set_instance_parameter_value directphy_f_0 {fgt_rx_serdes_pre_coding_enable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_serdes_lpbk_mode} {LOOPBACK_MODE_DISABLED}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_bw_sel} {LOW}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_cascade_enable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_frac_mode_enable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_k_cnt} {0}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_l_cnt} {1}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_m_cnt} {165}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_manual_enable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_n_cnt} {4}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_refclk_freq_itxt} $rclk_freq_mhz
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_refclk_freq_mhz} $rclk_freq_mhz
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_txuserclk1_enable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_txuserclk2_enable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_txuserclk_div} {100}
	set_instance_parameter_value directphy_f_0 {fgt_tx_pll_type} {FAST}
	set_instance_parameter_value directphy_f_0 {fgt_tx_serdes_disable} {0}
	set_instance_parameter_value directphy_f_0 {fgt_tx_serdes_gray_coding_enable} {1}
	set_instance_parameter_value directphy_f_0 {fgt_tx_serdes_prbs_gen_mode} {disable}
	set_instance_parameter_value directphy_f_0 {fgt_tx_serdes_pre_coding_enable} {0}
	set_instance_parameter_value directphy_f_0 {l_av1_enable} {0}
	set_instance_parameter_value directphy_f_0 {l_fec_mode} {IEEE 802.3 RS(528,514) (CL 91,KR)}
	set_instance_parameter_value directphy_f_0 {message_level} {error}
	set_instance_parameter_value directphy_f_0 {num_sys_cop} {1}
	set_instance_parameter_value directphy_f_0 {num_xcvr_per_sys} {1}
	set_instance_parameter_value directphy_f_0 {pldif_rx_clkout2_div} {2}
	set_instance_parameter_value directphy_f_0 {pldif_rx_clkout2_sel} {RX_WORD_CLK}
	set_instance_parameter_value directphy_f_0 {pldif_rx_clkout_sel} {RX_WORD_CLK}
	set_instance_parameter_value directphy_f_0 {pldif_rx_coreclkin_clock_network} {dedicated}
	set_instance_parameter_value directphy_f_0 {pldif_rx_double_width_transfer_enable} {1}
	set_instance_parameter_value directphy_f_0 {pldif_rx_fast_pipeln_reg_enable} {0}
	set_instance_parameter_value directphy_f_0 {pldif_rx_fifo_mode} {phase_comp}
	set_instance_parameter_value directphy_f_0 {pldif_rx_fifo_pempty_thld} {2}
	set_instance_parameter_value directphy_f_0 {pldif_rx_fifo_pfull_thld} {10}
	set_instance_parameter_value directphy_f_0 {pldif_tile_tx_fifo_mode} {phase_comp}
	set_instance_parameter_value directphy_f_0 {pldif_tx_clkout2_div} {2}
	set_instance_parameter_value directphy_f_0 {pldif_tx_clkout2_sel} {TX_WORD_CLK}
	set_instance_parameter_value directphy_f_0 {pldif_tx_clkout_sel} {TX_WORD_CLK}
	set_instance_parameter_value directphy_f_0 {pldif_tx_coreclkin2_clock_network} {dedicated}
	set_instance_parameter_value directphy_f_0 {pldif_tx_coreclkin_clock_network} {dedicated}
	set_instance_parameter_value directphy_f_0 {pldif_tx_double_width_transfer_enable} {1}
	set_instance_parameter_value directphy_f_0 {pldif_tx_fast_pipeln_reg_enable} {0}
	set_instance_parameter_value directphy_f_0 {pldif_tx_fifo_mode} {phase_comp}
	set_instance_parameter_value directphy_f_0 {pldif_tx_fifo_pempty_thld} {2}
	set_instance_parameter_value directphy_f_0 {pldif_tx_fifo_pfull_thld} {10}
	set_instance_parameter_value directphy_f_0 {pma_data_rate} $line_rate_mbps
	set_instance_parameter_value directphy_f_0 {pma_modulation} {NRZ}
	set_instance_parameter_value directphy_f_0 {pma_width} {20}
	set_instance_parameter_value directphy_f_0 {pmaif_lpbk_enable} {0}
	set_instance_parameter_value directphy_f_0 {pmaif_rx_fifo_mode_s} {register}
	set_instance_parameter_value directphy_f_0 {pmaif_tx_fifo_mode_s} {phase_comp}
	set_instance_parameter_value directphy_f_0 {protocol_hard_pcie_lowloss} {DISABLE}
	set_instance_parameter_value directphy_f_0 {refclk_cwbin_gui} {100.0}
	set_instance_parameter_value directphy_f_0 {rx_ac_couple_enable} {ENABLE}
	set_instance_parameter_value directphy_f_0 {rx_deskew_en} {0}
	set_instance_parameter_value directphy_f_0 {rx_onchip_termination} {RX_ONCHIP_TERMINATION_R_2}
	set_instance_parameter_value directphy_f_0 {rxeq_dfe_data_tap_1} {0}
	set_instance_parameter_value directphy_f_0 {rxeq_hf_boost} {0}
	set_instance_parameter_value directphy_f_0 {rxeq_vga_gain} {0}
	set_instance_parameter_value directphy_f_0 {src_bypass} {0}
	set_instance_parameter_value directphy_f_0 {suppress_design_example_messages} {0}
	set_instance_parameter_value directphy_f_0 {syspll_outclk_freq_mhz} {830.08}
	set_instance_parameter_value directphy_f_0 {tx_custom_cadence_enable} {0}
	set_instance_parameter_value directphy_f_0 {ux_txeq_main_tap} {50}
	set_instance_parameter_value directphy_f_0 {ux_txeq_post_tap_1} {0}
	set_instance_parameter_value directphy_f_0 {ux_txeq_pre_tap_1} {5}
	set_instance_parameter_value directphy_f_0 {ux_txeq_pre_tap_2} {0}
	set_instance_parameter_value directphy_f_0 {vsr_mode} {VSR_MODE_DISABLE}
	set_instance_parameter_value directphy_f_0 {xcvr_type} {FGT}
	set_instance_property directphy_f_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property rx_cdr_refclk_link EXPORT_OF directphy_f_0.rx_cdr_refclk_link
	set_interface_property tx_pll_refclk_link EXPORT_OF directphy_f_0.tx_pll_refclk_link
	set_interface_property tx_reset EXPORT_OF directphy_f_0.tx_reset
	set_interface_property rx_reset EXPORT_OF directphy_f_0.rx_reset
	set_interface_property tx_reset_ack EXPORT_OF directphy_f_0.tx_reset_ack
	set_interface_property rx_reset_ack EXPORT_OF directphy_f_0.rx_reset_ack
	set_interface_property tx_ready EXPORT_OF directphy_f_0.tx_ready
	set_interface_property rx_ready EXPORT_OF directphy_f_0.rx_ready
	set_interface_property tx_coreclkin EXPORT_OF directphy_f_0.tx_coreclkin
	set_interface_property rx_coreclkin EXPORT_OF directphy_f_0.rx_coreclkin
	set_interface_property tx_clkout EXPORT_OF directphy_f_0.tx_clkout
	set_interface_property tx_clkout2 EXPORT_OF directphy_f_0.tx_clkout2
	set_interface_property rx_clkout EXPORT_OF directphy_f_0.rx_clkout
	set_interface_property rx_clkout2 EXPORT_OF directphy_f_0.rx_clkout2
	set_interface_property tx_serial_data EXPORT_OF directphy_f_0.tx_serial_data
	set_interface_property tx_serial_data_n EXPORT_OF directphy_f_0.tx_serial_data_n
	set_interface_property rx_serial_data EXPORT_OF directphy_f_0.rx_serial_data
	set_interface_property rx_serial_data_n EXPORT_OF directphy_f_0.rx_serial_data_n
	set_interface_property tx_pll_locked EXPORT_OF directphy_f_0.tx_pll_locked
	set_interface_property rx_is_lockedtodata EXPORT_OF directphy_f_0.rx_is_lockedtodata
	set_interface_property rx_is_lockedtoref EXPORT_OF directphy_f_0.rx_is_lockedtoref
	set_interface_property tx_fifo_full EXPORT_OF directphy_f_0.tx_fifo_full
	set_interface_property tx_fifo_empty EXPORT_OF directphy_f_0.tx_fifo_empty
	set_interface_property tx_pmaif_fifo_empty EXPORT_OF directphy_f_0.tx_pmaif_fifo_empty
	set_interface_property tx_pmaif_fifo_pempty EXPORT_OF directphy_f_0.tx_pmaif_fifo_pempty
	set_interface_property tx_pmaif_fifo_pfull EXPORT_OF directphy_f_0.tx_pmaif_fifo_pfull
	set_interface_property tx_parallel_data EXPORT_OF directphy_f_0.tx_parallel_data
	set_interface_property rx_parallel_data EXPORT_OF directphy_f_0.rx_parallel_data

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="directphy_f_0">
  <datum __value="_sortIndex" value="0" type="int" />
 </element>
</bonusData>
}
	set_module_property FILE {qeciphy_ftile.ip}
	set_module_property GENERATION_ID {0x00000000}
	set_module_property NAME {qeciphy_ftile}

	# save the system
	sync_sysinfo_parameters
	save_system qeciphy_ftile
}

proc do_set_exported_interface_sysinfo_parameters {} {
}

# create all the systems, from bottom up
do_create_qeciphy_ftile

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
