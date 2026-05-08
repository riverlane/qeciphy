package require -exact qsys 25.3.1

# create the system "sys_clk_100"
proc do_create_sys_clk_100 {} {
	# create the system
	create_system sys_clk_100
	set_project_property BOARD {default}
	set_project_property DEVICE {AGFB014R24B2E2V}
	set_project_property DEVICE_FAMILY {Agilex 7}
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance intelclkctrl_0 intelclkctrl 2.0.1
	set_instance_parameter_value intelclkctrl_0 {CLOCK_DIVIDER} {0}
	set_instance_parameter_value intelclkctrl_0 {CLOCK_DIVIDER_OUTPUTS} {1}
	set_instance_parameter_value intelclkctrl_0 {ENABLE} {0}
	set_instance_parameter_value intelclkctrl_0 {ENABLE_REGISTER_TYPE} {1}
	set_instance_parameter_value intelclkctrl_0 {ENABLE_TYPE} {2}
	set_instance_parameter_value intelclkctrl_0 {GLITCH_FREE_SWITCHOVER} {1}
	set_instance_parameter_value intelclkctrl_0 {NUM_CLOCKS} {1}
	set_instance_property intelclkctrl_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property inclk EXPORT_OF intelclkctrl_0.inclk
	set_interface_property outclk EXPORT_OF intelclkctrl_0.outclk

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="intelclkctrl_0">
  <datum __value="_sortIndex" value="0" type="int" />
 </element>
</bonusData>
}
	set_module_property FILE {sys_clk_100.ip}
	set_module_property GENERATION_ID {0x00000000}
	set_module_property NAME {sys_clk_100}

	# save the system
	sync_sysinfo_parameters
	save_system sys_clk_100
}

proc do_set_exported_interface_sysinfo_parameters {} {
}

# create all the systems, from bottom up
do_create_sys_clk_100

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
