# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2026 Riverlane Ltd.
#
# Creates a minimal Quartus project for IP generation.
#
# Called from Makefile quartus_generate_ip target via:
#   quartus_sh --script scripts/quartus_ip_gen_proj.tcl -tclargs \
#       <proj_dir> <proj_name> <family> <device>
#
# argv[0]  = proj_dir    absolute path where the project should be created
# argv[1]  = proj_name   e.g. altera_ip_gen
# argv[2]  = family      e.g. Agilex 7
# argv[3]  = device      e.g. AGFB014R24B2E2V

package require ::quartus::project

if {[llength $argv] > 0 && [string match "*tcl*" [lindex $argv 0]]} {
    set argv [lrange $argv 1 end]
}

if {[llength $argv] < 4} {
    puts "ERROR: quartus_ip_gen_proj.tcl requires 4 arguments: proj_dir proj_name family device"
    exit 1
}

set proj_dir  [lindex $argv 0]
set proj_name [lindex $argv 1]
set family    [lindex $argv 2]
set device    [lindex $argv 3]

file mkdir [file join $proj_dir "ip"]
cd $proj_dir
project_new -revision $proj_name $proj_name
set_global_assignment -name FAMILY "$family"
set_global_assignment -name DEVICE "$device"
export_assignments
project_close
puts "INFO: Created project '$proj_name' in $proj_dir"
