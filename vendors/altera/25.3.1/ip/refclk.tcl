package require -exact qsys 25.3.1

# --- Parameters: overridden by $argv when called from quartus_ip.tcl ---
set device         "AGIB027R31B1E1V"
set device_family  "Agilex 7"
set rclk_freq_mhz  156.25

if {[llength $argv] >= 1} { set device         [lindex $argv 0] }
if {[llength $argv] >= 2} { set device_family  [lindex $argv 1] }
if {[llength $argv] >= 4} { set rclk_freq_mhz  [lindex $argv 3] }

# create the system "refclk"
proc do_create_refclk {} {
	global device device_family rclk_freq_mhz
	# create the system
	create_system refclk
	set_project_property BOARD {default}
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $device_family
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance systemclk_f_0 systemclk_f 4.0.3
	set_instance_parameter_value systemclk_f_0 {bk_cfg_kvcc_vreg_offset_en_val} {CFG_KVCC_VREG_OFFSET_EN_VAL_DISABLE}
	set_instance_parameter_value systemclk_f_0 {bk_ext_ac_cap} {EXTERNAL_AC_CAP_ENABLE}
	set_instance_parameter_value systemclk_f_0 {bk_rx_invert_p_and_n} {RX_INVERT_PN_DIS}
	set_instance_parameter_value systemclk_f_0 {bk_rx_termination} {RXTERM_OFFSET_P0}
	set_instance_parameter_value systemclk_f_0 {bk_tx_invert_p_and_n} {TX_INVERT_PN_DIS}
	set_instance_parameter_value systemclk_f_0 {bk_tx_termination} {TXTERM_OFFSET_P0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_main_tap} {41.5}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_post_tap_1} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_post_tap_2} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_post_tap_3} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_post_tap_4} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_pre_tap_1} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_pre_tap_2} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_pre_tap_3} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txout_tristate_en} {TXOUT_TRISTATE_DIS}
	set_instance_parameter_value systemclk_f_0 {cmnpll_dummy} {0}
	set_instance_parameter_value systemclk_f_0 {cmnpll_enable_0} {0}
	set_instance_parameter_value systemclk_f_0 {cmnpll_enable_1} {0}
	set_instance_parameter_value systemclk_f_0 {cmnpll_refclk_src_0} {FHT RefClk #0}
	set_instance_parameter_value systemclk_f_0 {cmnpll_refclk_src_1} {FHT RefClk #0}
	set_instance_parameter_value systemclk_f_0 {cmnpll_xtensa_src} {Auto}
	set_instance_parameter_value systemclk_f_0 {protocol_hard_pcie_lowloss} {DISABLE}
	set_instance_parameter_value systemclk_f_0 {refclk_cdrclk_output_enable_0} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_cdrclk_output_enable_1} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_0} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_1} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_2} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_3} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_4} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_5} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_6} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_7} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_8} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_9} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_0} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_1} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_2} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_3} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_4} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_5} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_6} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_7} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_8} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_9} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_0} $rclk_freq_mhz
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_1} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_2} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_3} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_4} $rclk_freq_mhz
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_5} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_6} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_7} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_8} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_9} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_0} $rclk_freq_mhz
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_1} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_2} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_3} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_4} $rclk_freq_mhz
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_5} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_6} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_7} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_8} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_9} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_0} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_1} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_2} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_3} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_4} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_5} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_6} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_7} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_8} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_9} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fht_freq_mhz_txt_0} {}
	set_instance_parameter_value systemclk_f_0 {refclk_fht_freq_mhz_txt_1} {}
	set_instance_parameter_value systemclk_f_0 {rx_ac_couple_enable} {ENABLE}
	set_instance_parameter_value systemclk_f_0 {rx_onchip_termination} {RX_ONCHIP_TERMINATION_R_2}
	set_instance_parameter_value systemclk_f_0 {rxeq_dfe_data_tap_1} {0}
	set_instance_parameter_value systemclk_f_0 {rxeq_hf_boost} {0}
	set_instance_parameter_value systemclk_f_0 {rxeq_vga_gain} {0}
	set_instance_parameter_value systemclk_f_0 {syspll_flux_src} {Auto}
	set_instance_parameter_value systemclk_f_0 {syspll_freq_mhz_0} $rclk_freq_mhz
	set_instance_parameter_value systemclk_f_0 {syspll_freq_mhz_1} {805.6640625}
	set_instance_parameter_value systemclk_f_0 {syspll_freq_mhz_2} {805.6640625}
	set_instance_parameter_value systemclk_f_0 {syspll_mod_0} {User Configuration}
	set_instance_parameter_value systemclk_f_0 {syspll_mod_1} {Disabled}
	set_instance_parameter_value systemclk_f_0 {syspll_mod_2} {Disabled}
	set_instance_parameter_value systemclk_f_0 {syspll_refclk_src_0} {RefClk #4}
	set_instance_parameter_value systemclk_f_0 {syspll_refclk_src_1} {RefClk #0}
	set_instance_parameter_value systemclk_f_0 {syspll_refclk_src_2} {RefClk #0}
	set_instance_parameter_value systemclk_f_0 {ux_txeq_main_tap} {35}
	set_instance_parameter_value systemclk_f_0 {ux_txeq_post_tap_1} {0}
	set_instance_parameter_value systemclk_f_0 {ux_txeq_pre_tap_1} {5}
	set_instance_parameter_value systemclk_f_0 {ux_txeq_pre_tap_2} {0}
	set_instance_parameter_value systemclk_f_0 {vsr_mode} {VSR_MODE_DISABLE}
	set_instance_property systemclk_f_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property out_systempll_synthlock_0 EXPORT_OF systemclk_f_0.out_systempll_synthlock_0
	set_interface_property out_systempll_clk_0 EXPORT_OF systemclk_f_0.out_systempll_clk_0
	set_interface_property out_refclk_fgt_4 EXPORT_OF systemclk_f_0.out_refclk_fgt_4
	set_interface_property refclk_fgt EXPORT_OF systemclk_f_0.refclk_fgt
	set_interface_property disable_refclk_monitor_4 EXPORT_OF systemclk_f_0.disable_refclk_monitor_4

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="systemclk_f_0">
  <datum __value="_sortIndex" value="0" type="int" />
 </element>
</bonusData>
}
	set_module_property FILE {refclk.ip}
	set_module_property GENERATION_ID {0x00000000}
	set_module_property NAME {refclk}

	# save the system
	sync_sysinfo_parameters
	save_system refclk
}

proc do_set_exported_interface_sysinfo_parameters {} {
}

# create all the systems, from bottom up
do_create_refclk

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
