#!/usr/bin/env vivado -mode batch -source

# Script to generate simulation files for a single IP core XCI file
# Usage: vivado -mode batch -source vivado_sim_export.tcl -tclargs <part> <xci_file> <sim> <export_base_dir>

# Error handling
proc die {msg} { puts $msg; exit 1 }

# Parse arguments
if { !([info exists ::argv] && [llength $::argv] >= 4) } {
    die "ERROR: Usage: vivado -mode batch -source vivado_sim_export.tcl -tclargs <part> <xci_file> <sim> <export_base_dir>"
}

set part [lindex $::argv 0]
set xci_file [lindex $::argv 1]
set sim [lindex $::argv 2]
set export_base_dir [lindex $::argv 3]

puts "INFO: Using part: $part"
puts "INFO: XCI file: $xci_file"
puts "INFO: Simulator: $sim"
puts "INFO: Export base directory: $export_base_dir"

set xci_name [file rootname [file tail $xci_file]]
    
# Create temporary project for this specific XCI in the export base directory
set temp_project_name "temp_project_$xci_name"
set temp_project_dir [file join $export_base_dir $temp_project_name]

# Remove existing project if it exists
if {[file isdirectory $temp_project_dir]} {
    file delete -force $temp_project_dir
}

create_project $temp_project_name $temp_project_dir -part $part -force
set_property target_language Verilog [current_project]

import_ip $xci_file -name $xci_name

# Upgrade IP if needed and generate simulation targets
upgrade_ip [get_ips] -quiet
generate_target {simulation} [get_ips] -force
update_compile_order -fileset sources_1

# Export simulation files for this specific XCI
set export_dir [file join $temp_project_dir "sim_export"]
puts "INFO: Exporting simulation files for $xci_name to temporary location"
export_simulation -of_objects [get_ips] -simulator $sim -directory $export_dir -force


# Close the temporary project
close_project
