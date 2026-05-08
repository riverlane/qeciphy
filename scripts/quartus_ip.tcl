# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2026 Riverlane Ltd.
#
# quartus_ip.tcl — Variant-aware Altera IP generator.
#
# Called from Makefile quartus_synth target via:
#   quartus_sh --script scripts/quartus_ip.tcl -tclargs \
#       <variant> <device> <device_family> <project_name> <line_rate_mbps> <rclk_freq_mhz>
#
# Navigates to run/<project_name>/ip/, then runs qsys-script for each applicable
# IP script in vendors/altera/25.3/, passing device/family/rate params via --cmd.

package require ::quartus::project

# ---------------------------------------------------------------------------
# Parse arguments
# ---------------------------------------------------------------------------
# quartus_sh --script puts the script path as argv[0]; strip it.
if {[llength $argv] > 0 && [string match "*tcl*" [lindex $argv 0]]} {
    set argv [lrange $argv 1 end]
}

if {[llength $argv] < 6} {
    puts "ERROR: quartus_ip.tcl requires 6 arguments:"
    puts "  variant device device_family project_name line_rate_mbps rclk_freq_mhz"
    exit 1
}

set variant        [lindex $argv 0]
set device         [lindex $argv 1]
set device_family  [lindex $argv 2]
set proj_name      [lindex $argv 3]
set line_rate_mbps [lindex $argv 4]
set rclk_freq_mhz  [lindex $argv 5]

# ---------------------------------------------------------------------------
# Vendor directory and version
# ---------------------------------------------------------------------------
set start_dir  [pwd]
set vendor_dir [file join $start_dir "vendors" "altera" "25.3"]

if {![file isdirectory $vendor_dir]} {
    puts "ERROR: Vendor directory not found: $vendor_dir"
    exit 1
}

# ---------------------------------------------------------------------------
# Variant exclusion — scripts that must NOT run for a given variant
# ---------------------------------------------------------------------------
set etile_only_scripts {qeciphy_etile.tcl}
set ftile_only_scripts {qeciphy_ftile.tcl refclk.tcl}

switch -- [string toupper $variant] {
    "ETILE" { set excluded_scripts $ftile_only_scripts }
    "FTILE" { set excluded_scripts $etile_only_scripts }
    default {
        puts "ERROR: Unknown variant '$variant'. Must be ETILE or FTILE."
        exit 1
    }
}

# ---------------------------------------------------------------------------
# Navigate to run/<project_name>/ip/
# ---------------------------------------------------------------------------
set ip_dir [file join $start_dir "run" $proj_name "ip"]
file mkdir $ip_dir
cd $ip_dir
puts "INFO: Changed to IP directory: [pwd]"

set qpf_path [file normalize [file join ".." "${proj_name}.qpf"]]

# ---------------------------------------------------------------------------
# Run applicable IP scripts
# ---------------------------------------------------------------------------
set tcl_files [lsort [glob -nocomplain -directory $vendor_dir "*.tcl"]]

if {[llength $tcl_files] == 0} {
    puts "WARNING: No .tcl files found in $vendor_dir"
}

set param_cmd "set argv \[list {$device} {$device_family} $line_rate_mbps $rclk_freq_mhz\]"

set any_failed 0

foreach script_path $tcl_files {
    set script_name [file tail $script_path]

    if {[lsearch $excluded_scripts $script_name] >= 0} {
        puts "INFO: Skipping $script_name (excluded for variant $variant)"
        continue
    }

    puts "INFO: Generating IP from $script_name ..."
    if {[catch {
        exec qsys-script \
            --script=[file normalize $script_path] \
            --quartus-project=$qpf_path \
            --cmd=$param_cmd \
            2>@stdout
    } result]} {
        puts "ERROR: qsys-script failed for $script_name: $result"
        set any_failed 1
    } else {
        puts "INFO: Done: $script_name"
    }
}

if {$any_failed} {
    puts "ERROR: One or more IP generation scripts failed. Aborting."
    exit 1
}

# ---------------------------------------------------------------------------
# Return to start directory
# ---------------------------------------------------------------------------
cd $start_dir
puts "INFO: Returned to: [pwd]"
puts "INFO: quartus_ip.tcl complete."
