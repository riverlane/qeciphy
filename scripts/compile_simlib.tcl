#!/usr/bin/env tclsh

# Compile Xilinx Simulation Libraries
# Usage: vivado -mode batch -source compile_simlib.tcl -tclargs <simulator> <output_dir>

if { $argc != 2 } {
    puts "ERROR: Invalid arguments"
    puts "Usage: vivado -mode batch -source compile_simlib.tcl -tclargs <simulator> <output_dir>"
    puts "  simulator: vcs"
    puts "  output_dir: Directory where compiled libraries will be stored"
    exit 1
}

set simulator [lindex $argv 0]
set output_dir [lindex $argv 1]

puts "INFO: Compiling simulation libraries for $simulator"
puts "INFO: Output directory: $output_dir"

# Validate simulator
if { ![string match -nocase "vcs" $simulator] } {
    puts "ERROR: Unsupported simulator '$simulator'"
    puts "Supported simulator: vcs"
    exit 1
}

# Create output directory if it doesn't exist
file mkdir $output_dir

# Compile simulation libraries
puts "INFO: Starting compile_simlib..."
compile_simlib \
  -simulator $simulator \
  -directory $output_dir \
  -family all \
  -language all \
  -no_systemc_compile \
  -no_ip_compile

puts "INFO: Simulation libraries compiled successfully"
puts "INFO: Libraries located at: $output_dir"