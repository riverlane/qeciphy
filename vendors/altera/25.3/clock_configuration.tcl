package require -exact qsys 25.3

# create the system "clock_configuration"
proc do_create_clock_configuration {} {
	# create the system
	create_system clock_configuration
	set_project_property BOARD {default}
	set_project_property DEVICE {AGIB027R31B1E1V}
	set_project_property DEVICE_FAMILY {Agilex 7}
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance s10_configuration_clock_0 altera_s10_configuration_clock 19.1.6
	set_instance_parameter_value s10_configuration_clock_0 {CBX_AUTO_BLACKBOX} {ALL}
	set_instance_property s10_configuration_clock_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property clkout EXPORT_OF s10_configuration_clock_0.clkout

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="s10_configuration_clock_0">
  <datum __value="_sortIndex" value="0" type="int" />
 </element>
</bonusData>
}
	set_module_property FILE {clock_configuration.ip}
	set_module_property GENERATION_ID {0x00000000}
	set_module_property NAME {clock_configuration}

	# save the system
	sync_sysinfo_parameters
	save_system clock_configuration
}

proc do_set_exported_interface_sysinfo_parameters {} {
}

# create all the systems, from bottom up
do_create_clock_configuration

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
