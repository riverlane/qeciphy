package require -exact qsys 25.3

# create the system "qeciphy_rx_ila"
proc do_create_qeciphy_rx_ila {} {
	# create the system
	create_system qeciphy_rx_ila
	set_project_property BOARD {default}
	set_project_property DEVICE {AGIB027R31B1E1V}
	set_project_property DEVICE_FAMILY {Agilex 7}
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance signaltap_ii_logic_analyzer_0 altera_signaltap_ii_logic_analyzer 19.2.0
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_COUNTER_PIPELINE} {0}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_DATA_BITS} {80}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_ENABLE_ADVANCED_TRIGGER} {0}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_INCREMENTAL_ROUTING} {0}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_NODE_CRC_BITS} {32}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_NODE_INFO} {806383104}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_PIPELINE_FACTOR} {0}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_RAM_PIPELINE} {0}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_SAMPLE_DEPTH} {1024}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_STORAGE_QUALIFIER_GAP_RECORD} {0}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_TRIGGER_BITS} {80}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_TRIGGER_IN_ENABLED} {0}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_TRIGGER_LEVEL} {2}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_TRIGGER_LEVEL_PIPELINE} {1}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {SLD_TRIGGER_PIPELINE} {0}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {gui_num_segments} {2}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {gui_ram_type} {AUTO}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {gui_sq} {Continuous}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {gui_trigger_out_enabled} {0}
	set_instance_parameter_value signaltap_ii_logic_analyzer_0 {gui_use_segmented} {0}
	set_instance_property signaltap_ii_logic_analyzer_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property tap EXPORT_OF signaltap_ii_logic_analyzer_0.tap
	set_interface_property acq_clk EXPORT_OF signaltap_ii_logic_analyzer_0.acq_clk

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="signaltap_ii_logic_analyzer_0">
  <datum __value="_sortIndex" value="0" type="int" />
 </element>
</bonusData>
}
	set_module_property FILE {qeciphy_rx_ila.ip}
	set_module_property GENERATION_ID {0x00000000}
	set_module_property NAME {qeciphy_rx_ila}

	# save the system
	sync_sysinfo_parameters
	save_system qeciphy_rx_ila
}

proc do_set_exported_interface_sysinfo_parameters {} {
}

# create all the systems, from bottom up
do_create_qeciphy_rx_ila

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
