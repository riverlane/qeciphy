# Vivado version check
set scripts_vivado_version 2024.1
set current_vivado_version [version -short]
if { [string first $scripts_vivado_version $current_vivado_version] == -1 } {
  puts "WARNING: Script was generated in Vivado $scripts_vivado_version, running in $current_vivado_version."
  puts "If you encounter issues, open the IP in Vivado and upgrade it if needed."
}

# Parse arguments
if { !([info exists ::argv] && [llength $::argv] >= 8) } {
  puts "ERROR: Usage: vivado -mode batch -source vendor/xilinx/qeciphy_gtx_transceiver.tcl \\"
  puts "                -tclargs <part_number> <output_dir> <GT_LOC> <FCLK_FREQ> <RCLK_FREQ> <RX_RCLK_SRC> <TX_RCLK_SRC> <LINE_RATE_GBPS>"
  return 1
}

set part_number     [lindex $::argv 0]
set output_dir      [lindex $::argv 1]
set GT_LOC          [lindex $::argv 2]
set FCLK_FREQ       [lindex $::argv 3]
set RCLK_FREQ       [lindex $::argv 4]
set RX_RCLK_SRC     [lindex $::argv 5]
set TX_RCLK_SRC     [lindex $::argv 6]
set LINE_RATE_GBPS  [lindex $::argv 7]

puts "INFO: Using part number: $part_number"
puts "INFO: Output directory: $output_dir"
puts "INFO: GT Location: $GT_LOC"
puts "INFO: Reference clock frequency: $RCLK_FREQ MHz"
puts "INFO: Free-running clock frequency: $FCLK_FREQ MHz"
puts "INFO: RX reference clock source: $RX_RCLK_SRC"
puts "INFO: TX reference clock source: $TX_RCLK_SRC"
puts "INFO: Line rate: $LINE_RATE_GBPS Gbps"

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
set required_ips { xilinx.com:ip:gtwizard:3.6 }
foreach ip_vlnv $required_ips {
  set ip_obj [get_ipdefs -all $ip_vlnv]
  if { $ip_obj eq "" } {
    puts "ERROR: Missing IP $ip_vlnv in catalog. Add repository or install missing IP."
    return 1
  }
}

# Create IP qeciphy_gtx_transceiver
set ip_name qeciphy_gtx_transceiver
set ip_obj [create_ip -name gtwizard -vendor xilinx.com -library ip -version 3.6 -module_name $ip_name]

# Set IP parameters (customize as needed)
set_property -dict [list \
  CONFIG.advanced_clocking {false} \
  CONFIG.gt0_usesharedlogic {0} \
  CONFIG.gt0_val {true} \
  CONFIG.gt0_val_align_comma_double {false} \
  CONFIG.gt0_val_align_comma_enable {1111111111} \
  CONFIG.gt0_val_align_comma_word {Four_Byte_Boundaries} \
  CONFIG.gt0_val_align_mcomma_det {false} \
  CONFIG.gt0_val_align_mcomma_value {1010000011} \
  CONFIG.gt0_val_align_pcomma_det {false} \
  CONFIG.gt0_val_align_pcomma_value {0101111100} \
  CONFIG.gt0_val_cb {false} \
  CONFIG.gt0_val_cc {false} \
  CONFIG.gt0_val_clk_cor_seq_1_1 {00000000} \
  CONFIG.gt0_val_clk_cor_seq_1_2 {00000000} \
  CONFIG.gt0_val_clk_cor_seq_1_3 {00000000} \
  CONFIG.gt0_val_clk_cor_seq_1_4 {00000000} \
  CONFIG.gt0_val_clk_cor_seq_2_1 {00000000} \
  CONFIG.gt0_val_clk_cor_seq_2_2 {00000000} \
  CONFIG.gt0_val_clk_cor_seq_2_3 {00000000} \
  CONFIG.gt0_val_clk_cor_seq_2_4 {00000000} \
  CONFIG.gt0_val_comma_preset {K28.5} \
  CONFIG.gt0_val_cpll_rxout_div {1} \
  CONFIG.gt0_val_cpll_txout_div {1} \
  CONFIG.gt0_val_dec_mcomma_detect {true} \
  CONFIG.gt0_val_dec_pcomma_detect {true} \
  CONFIG.gt0_val_dec_valid_comma_only {false} \
  CONFIG.gt0_val_decoding {8B/10B} \
  CONFIG.gt0_val_dfe_mode {LPM-Auto} \
  CONFIG.gt0_val_drp {true} \
  CONFIG.gt0_val_drp_clock [format "%.3f" $FCLK_FREQ] \
  CONFIG.gt0_val_encoding {8B/10B} \
  CONFIG.gt0_val_max_cb_level {7} \
  CONFIG.gt0_val_no_rx {false} \
  CONFIG.gt0_val_no_tx {false} \
  CONFIG.gt0_val_pcs_pcie_en {false} \
  CONFIG.gt0_val_pd_trans_time_from_p2 {60} \
  CONFIG.gt0_val_pd_trans_time_non_p2 {25} \
  CONFIG.gt0_val_pd_trans_time_to_p2 {100} \
  CONFIG.gt0_val_port_cominitdet {false} \
  CONFIG.gt0_val_port_comsasdet {false} \
  CONFIG.gt0_val_port_comwakedet {false} \
  CONFIG.gt0_val_port_loopback {true} \
  CONFIG.gt0_val_port_phystatus {false} \
  CONFIG.gt0_val_port_rxbufreset {false} \
  CONFIG.gt0_val_port_rxbufstatus {false} \
  CONFIG.gt0_val_port_rxbyteisaligned {false} \
  CONFIG.gt0_val_port_rxbyterealign {false} \
  CONFIG.gt0_val_port_rxcdrhold {false} \
  CONFIG.gt0_val_port_rxchariscomma {false} \
  CONFIG.gt0_val_port_rxcharisk {true} \
  CONFIG.gt0_val_port_rxcommadet {false} \
  CONFIG.gt0_val_port_rxdfereset {true} \
  CONFIG.gt0_val_port_rxlpmen {false} \
  CONFIG.gt0_val_port_rxmcommaalignen {false} \
  CONFIG.gt0_val_port_rxpcommaalignen {false} \
  CONFIG.gt0_val_port_rxpcsreset {false} \
  CONFIG.gt0_val_port_rxpmareset {true} \
  CONFIG.gt0_val_port_rxpolarity {false} \
  CONFIG.gt0_val_port_rxrate {false} \
  CONFIG.gt0_val_port_rxslide {true} \
  CONFIG.gt0_val_port_rxstatus {false} \
  CONFIG.gt0_val_port_rxvalid {false} \
  CONFIG.gt0_val_port_tx8b10bbypass {false} \
  CONFIG.gt0_val_port_txbufstatus {false} \
  CONFIG.gt0_val_port_txchardispmode {false} \
  CONFIG.gt0_val_port_txchardispval {false} \
  CONFIG.gt0_val_port_txcomfinish {false} \
  CONFIG.gt0_val_port_txcominit {false} \
  CONFIG.gt0_val_port_txcomsas {false} \
  CONFIG.gt0_val_port_txcomwake {false} \
  CONFIG.gt0_val_port_txdetectrx {false} \
  CONFIG.gt0_val_port_txelecidle {false} \
  CONFIG.gt0_val_port_txinhibit {false} \
  CONFIG.gt0_val_port_txpcsreset {false} \
  CONFIG.gt0_val_port_txpmareset {true} \
  CONFIG.gt0_val_port_txpolarity {false} \
  CONFIG.gt0_val_port_txprbsforceerr {false} \
  CONFIG.gt0_val_port_txprbssel {false} \
  CONFIG.gt0_val_port_txrate {false} \
  CONFIG.gt0_val_prbs_detector {false} \
  CONFIG.gt0_val_protocol_file {Start_from_scratch} \
  CONFIG.gt0_val_qpll_fbdiv {100} \
  CONFIG.gt0_val_qpll_refclk_div {1} \
  CONFIG.gt0_val_rx_buffer_bypass_mode {Auto} \
  CONFIG.gt0_val_rx_cm_trim {800} \
  CONFIG.gt0_val_rx_data_width {32} \
  CONFIG.gt0_val_rx_int_datawidth {40} \
  CONFIG.gt0_val_rx_line_rate $LINE_RATE_GBPS \
  CONFIG.gt0_val_rx_refclk $RX_RCLK_SRC \
  CONFIG.gt0_val_rx_reference_clock [format "%.3f" $RCLK_FREQ] \
  CONFIG.gt0_val_rx_termination_voltage {Programmable} \
  CONFIG.gt0_val_rxbuf_en {true} \
  CONFIG.gt0_val_rxcomma_deten {true} \
  CONFIG.gt0_val_rxprbs_err_loopback {false} \
  CONFIG.gt0_val_rxslide_mode {PCS} \
  CONFIG.gt0_val_rxusrclk {RXOUTCLK} \
  CONFIG.gt0_val_sata_e_idle_val {4} \
  CONFIG.gt0_val_sata_rx_burst_val {4} \
  CONFIG.gt0_val_tx_buffer_bypass_mode {Auto} \
  CONFIG.gt0_val_tx_data_width {32} \
  CONFIG.gt0_val_tx_int_datawidth {40} \
  CONFIG.gt0_val_tx_line_rate $LINE_RATE_GBPS \
  CONFIG.gt0_val_tx_refclk $TX_RCLK_SRC \
  CONFIG.gt0_val_tx_reference_clock [format "%.3f" $RCLK_FREQ] \
  CONFIG.gt0_val_txbuf_en {true} \
  CONFIG.gt0_val_txdiffctrl {false} \
  CONFIG.gt0_val_txmaincursor {false} \
  CONFIG.gt0_val_txpostcursor {false} \
  CONFIG.gt0_val_txprecursor {false} \
  CONFIG.gt0_val_txusrclk {TXOUTCLK} \
  CONFIG.gt1_val {false} \
  CONFIG.gt1_val_rx_refclk $RX_RCLK_SRC \
  CONFIG.gt1_val_tx_refclk $TX_RCLK_SRC \
  CONFIG.gt2_val {false} \
  CONFIG.gt2_val_rx_refclk $RX_RCLK_SRC \
  CONFIG.gt2_val_tx_refclk $TX_RCLK_SRC \
  CONFIG.gt3_val {false} \
  CONFIG.gt3_val_rx_refclk $RX_RCLK_SRC \
  CONFIG.gt3_val_tx_refclk $TX_RCLK_SRC \
  CONFIG.gt_val_drp {false} \
  CONFIG.gt_val_drp_clock [format "%.3f" $FCLK_FREQ] \
  CONFIG.gt_val_rx_pll {QPLL} \
  CONFIG.gt_val_tx_pll {QPLL} \
  CONFIG.identical_protocol_file {Start_from_scratch} \
  CONFIG.identical_val_no_rx {false} \
  CONFIG.identical_val_no_tx {false} \
  CONFIG.identical_val_rx_line_rate $LINE_RATE_GBPS \
  CONFIG.identical_val_rx_reference_clock [format "%.3f" $RCLK_FREQ] \
  CONFIG.identical_val_tx_line_rate $LINE_RATE_GBPS \
  CONFIG.identical_val_tx_reference_clock [format "%.3f" $RCLK_FREQ] \
] [get_ips $ip_name]

puts "INFO: IP core '$ip_name' generated successfully"

close_project
exit
