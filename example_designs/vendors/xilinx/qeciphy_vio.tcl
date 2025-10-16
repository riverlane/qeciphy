##################################################################
# Vivado Version Warning Only (Script is version-agnostic)
##################################################################
set scripts_vivado_version 2024.1
set current_vivado_version [version -short]
if { [string first $scripts_vivado_version $current_vivado_version] == -1 } {
  puts "WARNING: Script was generated in Vivado $scripts_vivado_version, running in $current_vivado_version."
  puts "If you encounter issues, open the IP in Vivado and upgrade it if needed."
}

##################################################################
# Accept part_number as argument (no longer need output_dir)
##################################################################
if { !([info exists ::argv] && [llength $::argv] >= 1) } {
  puts "ERROR: Usage: vivado -mode batch -source qeciphy_vio.tcl -tclargs <part_number>"
  return 1
}
set part_number [lindex $::argv 0]
puts "INFO: Using part number: $part_number"

##################################################################
# Check Required IPs
##################################################################
set required_ips { xilinx.com:ip:vio:3.0 }
foreach ip_vlnv $required_ips {
  set ip_obj [get_ipdefs -all $ip_vlnv]
  if { $ip_obj eq "" } {
    puts "ERROR: Missing IP $ip_vlnv in catalog. Add repository or install missing IP."
    return 1
  }
}

##################################################################
# Create IP qeciphy_vio in current project
##################################################################
set ip_name qeciphy_vio
puts "INFO: Creating IP core '$ip_name' in current project"

set ip_obj [create_ip -name vio -vendor xilinx.com -library ip -version 3.0 -module_name $ip_name]

# Set IP parameters (customize as needed)
set_property -dict [list \
  CONFIG.C_EN_PROBE_IN_ACTIVITY {0} \
  CONFIG.C_NUM_PROBE_IN {0} \
  CONFIG.C_NUM_PROBE_OUT {4} \
  CONFIG.C_PROBE_OUT0_INIT_VAL {0x1} \
  CONFIG.C_PROBE_OUT1_INIT_VAL {0x1} \
  CONFIG.C_PROBE_OUT3_INIT_VAL {0xf} \
  CONFIG.C_PROBE_OUT3_WIDTH {4} \
] [get_ips $ip_name]

puts "INFO: IP core '$ip_name' created successfully"