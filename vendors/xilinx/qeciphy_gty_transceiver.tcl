# Vivado version check
set scripts_vivado_version 2024.1
set current_vivado_version [version -short]
if { [string first $scripts_vivado_version $current_vivado_version] == -1 } {
  puts "WARNING: Script was generated in Vivado $scripts_vivado_version, running in $current_vivado_version."
  puts "If you encounter issues, open the IP in Vivado and upgrade it if needed."
}

# Parse arguments
if { !([info exists ::argv] && [llength $::argv] >= 8) } {
  puts "ERROR: Usage:"
  puts "  vivado -mode batch -source vendor/xilinx/qeciphy_gty_transceiver.tcl \\"
  puts "         -tclargs <part_number> <output_dir> <GT_LOC> <FCLK_FREQ> <RCLK_FREQ> <RX_RCLK_SRC> <TX_RCLK_SRC> <LINE_RATE_GBPS>"
  puts ""
  return 1
}

set part_number   [lindex $::argv 0]
set output_dir    [lindex $::argv 1]
set GT_LOC        [lindex $::argv 2]
set FCLK_FREQ     [lindex $::argv 3]
set RCLK_FREQ     [lindex $::argv 4]
set RX_RCLK_SRC   [lindex $::argv 5]
set TX_RCLK_SRC   [lindex $::argv 6]
set LINE_RATE_GBPS [lindex $::argv 7]

# Derive TXPROGDIV frequency in MHz:
#   F_progdiv = LineRate(Gbps) * 1000 / 40 (bits per internal clock @ 8b/10b, 32-bit user)
set TXPROGDIV_FREQ_VAL [expr {double($LINE_RATE_GBPS) * 1000.0 / 40.0}]
set TXPROGDIV_FREQ_VAL [format "%.3f" $TXPROGDIV_FREQ_VAL]

puts "INFO: Using part number: $part_number"
puts "INFO: Output directory: $output_dir"
puts "INFO: GT Location: $GT_LOC"
puts "INFO: Free-run clock frequency: $FCLK_FREQ"
puts "INFO: Reference clock frequency: $RCLK_FREQ"
puts "INFO: RX reference clock source: $RX_RCLK_SRC"
puts "INFO: TX reference clock source: $TX_RCLK_SRC"
puts "INFO: Line rate: $LINE_RATE_GBPS Gbps"
puts "INFO: TXPROGDIV frequency (derived): $TXPROGDIV_FREQ_VAL MHz"

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
set required_ips { xilinx.com:ip:gtwizard_ultrascale:1.7 }
foreach ip_vlnv $required_ips {
  set ip_obj [get_ipdefs -all $ip_vlnv]
  if { $ip_obj eq "" } {
    puts "ERROR: Missing IP $ip_vlnv in catalog. Add repository or install missing IP."
    return 1
  }
}

# Create IP qeciphy_gty_transceiver
set ip_name qeciphy_gty_transceiver
set ip_obj [create_ip -name gtwizard_ultrascale -vendor xilinx.com -library ip -version 1.7 -module_name $ip_name]

# Set IP parameters
set_property -dict [list \
  CONFIG.CHANNEL_ENABLE $GT_LOC \
  CONFIG.ENABLE_OPTIONAL_PORTS {qpll0lock_out rxsliderdy_out} \
  CONFIG.FREERUN_FREQUENCY $FCLK_FREQ \
  CONFIG.LOCATE_RX_USER_CLOCKING {EXAMPLE_DESIGN} \
  CONFIG.LOCATE_TX_USER_CLOCKING {EXAMPLE_DESIGN} \
  CONFIG.RX_BUFFER_MODE {1} \
  CONFIG.RX_CC_K_0_0 {false} \
  CONFIG.RX_CC_LEN_SEQ {1} \
  CONFIG.RX_CC_NUM_SEQ {0} \
  CONFIG.RX_CC_PERIODICITY {5000} \
  CONFIG.RX_CC_VAL_0_0 {00000000} \
  CONFIG.RX_COMMA_ALIGN_WORD {4} \
  CONFIG.RX_COMMA_SHOW_REALIGN_ENABLE {false} \
  CONFIG.RX_DATA_DECODING {8B10B} \
  CONFIG.RX_INT_DATA_WIDTH {40} \
  CONFIG.RX_JTOL_FC {7.4985003} \
  CONFIG.RX_LINE_RATE $LINE_RATE_GBPS \
  CONFIG.RX_MASTER_CHANNEL $GT_LOC \
  CONFIG.RX_OUTCLK_SOURCE {RXOUTCLKPMA} \
  CONFIG.RX_REFCLK_FREQUENCY $RCLK_FREQ \
  CONFIG.RX_REFCLK_SOURCE $RX_RCLK_SRC \
  CONFIG.RX_SLIDE_MODE {PMA} \
  CONFIG.RX_USER_DATA_WIDTH {32} \
  CONFIG.TXPROGDIV_FREQ_VAL $TXPROGDIV_FREQ_VAL \
  CONFIG.TX_BUFFER_MODE {1} \
  CONFIG.TX_DATA_ENCODING {8B10B} \
  CONFIG.TX_INT_DATA_WIDTH {40} \
  CONFIG.TX_LINE_RATE $LINE_RATE_GBPS \
  CONFIG.TX_MASTER_CHANNEL $GT_LOC \
  CONFIG.TX_OUTCLK_SOURCE {TXOUTCLKPMA} \
  CONFIG.TX_REFCLK_FREQUENCY $RCLK_FREQ \
  CONFIG.TX_REFCLK_SOURCE $TX_RCLK_SRC \
  CONFIG.TX_USER_DATA_WIDTH {32} \
] [get_ips $ip_name]

puts "INFO: IP core '$ip_name' generated successfully"

close_project
exit
