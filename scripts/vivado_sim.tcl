# SPDX-License-Identifier: LicenseRef-LICENSE
# Copyright (c) 2025 Riverlane Ltd.

# Vivado simulation script
# Usage: vivado -mode batch -source vivado_sim.tcl -tclargs <SIM_TOP> <PART> <VARIANT> <SRC_FILES> -- <SIM_FILES> -- <XCI_FILES>

if { !([info exists ::argv] && [llength $::argv] >= 3) } {
    puts "ERROR: Usage: vivado -mode batch -source vivado_sim.tcl -tclargs <SIM_TOP> <PART> <VARIANT> <SRC_FILES> -- <SIM_FILES> -- <XCI_FILES>"
    exit 1
}

set sim_top     [lindex $::argv 0]
set part_number [lindex $::argv 1] 
set variant     [lindex $::argv 2]

# Parse file arguments (separated by "--")
set separator_indices {}
for {set i 0} {$i < [llength $::argv]} {incr i} {
    if {[lindex $::argv $i] eq "--"} {
        lappend separator_indices $i
    }
}

if {[llength $separator_indices] == 0} {
    set src_files [lrange $::argv 3 end]
    set sim_files {}
    set xci_files {}
} elseif {[llength $separator_indices] == 1} {
    set sep1 [lindex $separator_indices 0]
    set src_files [lrange $::argv 3 [expr {$sep1 - 1}]]
    set sim_files [lrange $::argv [expr {$sep1 + 1}] end]
    set xci_files {}
} else {
    set sep1 [lindex $separator_indices 0]
    set sep2 [lindex $separator_indices 1]
    set src_files [lrange $::argv 3 [expr {$sep1 - 1}]]
    set sim_files [lrange $::argv [expr {$sep1 + 1}] [expr {$sep2 - 1}]]
    set xci_files [lrange $::argv [expr {$sep2 + 1}] end]
}

puts "INFO: Simulation top: $sim_top"
puts "INFO: Using part number: $part_number"
puts "INFO: Using variant: $variant"
puts "INFO: Source files: $src_files"
puts "INFO: Simulation files: $sim_files"
puts "INFO: XCI files: $xci_files"

# Create simulation project
set output_dir "./run/sim_qeciphy"
create_project qeciphy_sim $output_dir -part $part_number -force
set_property target_language Verilog [current_project]
set_property simulator_language Mixed [current_project]

# Add SVA bind include file
add_files -fileset sim_1 sva/binds/all_bind.svh

# Add source files
foreach f $src_files {
    if {$f ne ""} {
        add_files -fileset sources_1 $f
    }
}

# Add simulation files
foreach f $sim_files {
    if {$f ne ""} {
        add_files -fileset sim_1 $f
    }
}

# Add IP cores from XCI files
foreach f $xci_files {
    if {$f ne ""} {
        import_ip $f
    }
}

# Set simulation top module and configure runtime
set_property top $sim_top [get_filesets sim_1]
set_property -name {xsim.simulate.runtime} -value {1s} -objects [get_filesets sim_1]

# Pass variant define to simulation
set_property verilog_define "GT_TYPE=\"$variant\"" [get_filesets sim_1]

# Define XSIM for testbench conditional includes
set_property verilog_define "XSIM" [get_filesets sim_1]

# Update compile order and upgrade IPs
update_compile_order -fileset sources_1
upgrade_ip [get_ips]

# Launch simulation
if {[catch launch_simulation errorstring]} {
    puts "ERROR: Vivado - $errorstring"
} else {
    close_sim
}