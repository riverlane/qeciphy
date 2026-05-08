package require -exact qsys 25.3

# create the system "clock_divider"
proc do_create_clock_divider {} {
	# create the system
	create_system clock_divider
	set_project_property BOARD {default}
	set_project_property DEVICE {AGIB027R31B1E1V}
	set_project_property DEVICE_FAMILY {Agilex 7}
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance intelclkctrl_0 intelclkctrl 2.0.1
	set_instance_parameter_value intelclkctrl_0 {CLOCK_DIVIDER} {1}
	set_instance_parameter_value intelclkctrl_0 {CLOCK_DIVIDER_OUTPUTS} {2}
	set_instance_parameter_value intelclkctrl_0 {ENABLE} {0}
	set_instance_parameter_value intelclkctrl_0 {ENABLE_REGISTER_TYPE} {1}
	set_instance_parameter_value intelclkctrl_0 {ENABLE_TYPE} {2}
	set_instance_parameter_value intelclkctrl_0 {GLITCH_FREE_SWITCHOVER} {0}
	set_instance_parameter_value intelclkctrl_0 {NUM_CLOCKS} {1}
	set_instance_property intelclkctrl_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property inclk EXPORT_OF intelclkctrl_0.inclk
	set_interface_property clock_div1x EXPORT_OF intelclkctrl_0.clock_div1x
	set_interface_property clock_div2x EXPORT_OF intelclkctrl_0.clock_div2x

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="intelclkctrl_0">
  <datum __value="_sortIndex" value="0" type="int" />
 </element>
</bonusData>
}
	set_module_property FILE {clock_divider.ip}
	set_module_property GENERATION_ID {0x00000000}
	set_module_property NAME {clock_divider}

	# save the system
	sync_sysinfo_parameters
	save_system clock_divider
}

proc do_set_exported_interface_sysinfo_parameters {} {
}

# create all the systems, from bottom up
do_create_clock_divider

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
