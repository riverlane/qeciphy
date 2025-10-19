# Vivado version check
set scripts_vivado_version 2024.1
set current_vivado_version [version -short]
if { [string first $scripts_vivado_version $current_vivado_version] == -1 } {
  puts "WARNING: Script was generated in Vivado $scripts_vivado_version, running in $current_vivado_version."
  puts "If you encounter issues, open the IP in Vivado and upgrade it if needed."
}

# Parse arguments
if { !([info exists ::argv] && [llength $::argv] >= 2) } {
  puts "ERROR: Usage: vivado -mode batch -source vendor/xilinx/qeciphy_clk_mmcm.tcl -tclargs <part_number> <output_dir>"
  return 1
}
set part_number [lindex $::argv 0]
set output_dir [lindex $::argv 1]
puts "INFO: Using part number: $part_number"
puts "INFO: Output directory: $output_dir"

# Create project in output directory
if { [file exists $output_dir] } {
  foreach f [glob -nocomplain -directory $output_dir *] {
    file delete -force $f
  }
} else {
  file mkdir $output_dir
}

create_project temp_project $output_dir -part $part_number
set_property target_language Verilog [current_project]
set_property simulator_language Mixed [current_project]

# Check required IPs
set required_ips { xilinx.com:ip:clk_wiz:6.0 }
foreach ip_vlnv $required_ips {
  set ip_obj [get_ipdefs -all $ip_vlnv]
  if { $ip_obj eq "" } {
    puts "ERROR: Missing IP $ip_vlnv in catalog. Add repository or install missing IP."
    return 1
  }
}

# Create IP qeciphy_clk_mmcm
set ip_name qeciphy_clk_mmcm
set ip_obj [create_ip -name clk_wiz -vendor xilinx.com -library ip -version 6.0 -module_name $ip_name]

# Set IP parameters (customize as needed)
set_property -dict [list \
  CONFIG.CLKIN1_JITTER_PS {32.0} \
  CONFIG.CLKOUT1_JITTER {92.438} \
  CONFIG.CLKOUT1_PHASE_ERROR {82.557} \
  CONFIG.CLKOUT1_REQUESTED_OUT_FREQ {156.25} \
  CONFIG.CLKOUT2_JITTER {80.646} \
  CONFIG.CLKOUT2_PHASE_ERROR {82.557} \
  CONFIG.CLKOUT2_REQUESTED_OUT_FREQ {312.5} \
  CONFIG.CLKOUT2_USED {true} \
  CONFIG.CLK_OUT1_PORT {clk_out} \
  CONFIG.CLK_OUT2_PORT {clk_out_2x} \
  CONFIG.MMCM_CLKFBOUT_MULT_F {3.000} \
  CONFIG.MMCM_CLKIN1_PERIOD {3.200} \
  CONFIG.MMCM_CLKIN2_PERIOD {10.0} \
  CONFIG.MMCM_CLKOUT0_DIVIDE_F {6.000} \
  CONFIG.MMCM_CLKOUT1_DIVIDE {3} \
  CONFIG.MMCM_DIVCLK_DIVIDE {1} \
  CONFIG.NUM_OUT_CLKS {2} \
  CONFIG.PRIMARY_PORT {clk_in} \
  CONFIG.PRIM_IN_FREQ {312.5} \
  CONFIG.PRIM_SOURCE {Global_buffer} \
  CONFIG.USE_INCLK_STOPPED {true} \
  CONFIG.USE_LOCKED {false} \
] [get_ips $ip_name]

puts "INFO: IP core '$ip_name' generated successfully"

close_project
exit