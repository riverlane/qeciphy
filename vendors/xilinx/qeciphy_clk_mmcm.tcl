# Vivado version check
set scripts_vivado_version 2024.1
set current_vivado_version [version -short]
if { [string first $scripts_vivado_version $current_vivado_version] == -1 } {
  puts "WARNING: Script was generated in Vivado $scripts_vivado_version, running in $current_vivado_version."
  puts "If you encounter issues, open the IP in Vivado and upgrade it if needed."
}

# Parse arguments
if { !([info exists ::argv] && [llength $::argv] >= 3) } {
  puts "ERROR: Usage: vivado -mode batch -source vendor/xilinx/qeciphy_clk_mmcm.tcl \\"
  puts "                -tclargs <part_number> <output_dir> <LINE_RATE_GBPS>"
  return 1
}

set part_number    [lindex $::argv 0]
set output_dir     [lindex $::argv 1]
set LINE_RATE_GBPS [lindex $::argv 2]

# Derive clock frequencies
# GT internal/user clock for 32b @ 8b/10b:
#   F_TX_RX_CLK = LINE_RATE_GBPS * 1000 / 40 (MHz)
set F_TX_RX_CLK     [expr {double($LINE_RATE_GBPS) * 1000.0 / 40.0}]
set F_CLK_OUT2X  $F_TX_RX_CLK
set F_CLK_OUT    [expr {$F_TX_RX_CLK / 2.0}]

# Period for MMCM/PLL input in ns: 1000 / F_in(MHz)
set CLKIN1_PERIOD [expr {1000.0 / $F_TX_RX_CLK}]

puts "INFO: Using part number: $part_number"
puts "INFO: Output directory: $output_dir"
puts "INFO: Line rate: $LINE_RATE_GBPS Gbps"
puts "INFO: MMCM input (clk_in / clk_out_2x): [format \"%.3f\" $F_TX_RX_CLK] MHz"
puts "INFO: MMCM clk_out:                    [format \"%.3f\" $F_CLK_OUT] MHz"

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

set_property -dict [list \
  CONFIG.CLKIN1_JITTER_PS {32.0} \
  CONFIG.CLK_OUT1_PORT {clk_out} \
  CONFIG.CLK_OUT2_PORT {clk_out_2x} \
  CONFIG.CLKOUT1_REQUESTED_OUT_FREQ [format "%.3f" $F_CLK_OUT] \
  CONFIG.CLKOUT2_REQUESTED_OUT_FREQ [format "%.3f" $F_CLK_OUT2X] \
  CONFIG.CLKOUT2_USED {true} \
  CONFIG.MMCM_CLKIN1_PERIOD [format "%.3f" $CLKIN1_PERIOD] \
  CONFIG.NUM_OUT_CLKS {2} \
  CONFIG.PRIMARY_PORT {clk_in} \
  CONFIG.PRIM_IN_FREQ [format "%.3f" $F_TX_RX_CLK] \
  CONFIG.PRIM_SOURCE {Global_buffer} \
  CONFIG.USE_INCLK_STOPPED {true} \
  CONFIG.USE_LOCKED {false} \
] [get_ips $ip_name]

puts "INFO: IP core '$ip_name' generated successfully"

close_project
exit
