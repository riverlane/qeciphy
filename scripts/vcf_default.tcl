# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2025 Riverlane Ltd.

# VCF formal verification script
# Usage: vcf -f vcf_default.tcl

# Get OPT_TOP and OPT_MODE from environment
set OPT_TOP "$env(OPT_TOP)"
set OPT_MODE "$env(OPT_MODE)"

# Derive repo files from OPT_TOP
set CHECKER_FILE        "sva/checkers/${OPT_TOP}_checker.sv"
set BIND_FILE           "sva/binds/${OPT_TOP}_bind.sv"
set HARNESS_FILE        "formal/harness/${OPT_TOP}_harness.sv"
set DESIGN_SPECIFIC_TCL "formal/tcl/${OPT_TOP}.tcl"

# Formal harness
set DESIGN_TOP    "${OPT_TOP}_harness"

puts "INFO: OPT_TOP                 = $OPT_TOP"
puts "INFO: OPT_MODE                = $OPT_MODE"
puts "INFO: DESIGN_TOP              = $DESIGN_TOP"
puts "INFO: CHECKER_FILE            = $CHECKER_FILE"
puts "INFO: BIND_FILE               = $BIND_FILE"
puts "INFO: HARNESS_FILE            = $HARNESS_FILE"
puts "INFO: DESIGN_SPECIFIC_TCL     = $DESIGN_SPECIFIC_TCL"

# Check that required files exist
foreach f [list $CHECKER_FILE $BIND_FILE $HARNESS_FILE] {
  if {![file exists $f]} {
    puts "ERROR: Required file not found: $f"
    exit 1
  }
}

# Disable summary report
set_app_var generate_elab_summary_report false

# Set stop on synthesis error true
set_app_var stop_on_synth_error true

# Specify application
set_fml_appmode FPV

report_link

# Load design files
set vcs_args "-cm_libs vy"
append vcs_args " $env(VCF_FILES)"
append vcs_args " $HARNESS_FILE"

puts "INFO: Loading formal verification design: $DESIGN_TOP"
puts "INFO: VCS args: $vcs_args"

read_file -top $DESIGN_TOP -format sverilog -sva -vcs $vcs_args

# Set max time for formal run
set_fml_var fml_max_time      20M

# Run design specific TCL
if {[file exists $DESIGN_SPECIFIC_TCL]} {
    puts "INFO: Sourcing design-specific TCL: $DESIGN_SPECIFIC_TCL"
    source $DESIGN_SPECIFIC_TCL
} else {
    puts "INFO: No design-specific TCL found, continuing with default behavior"
}

# Bring the design out of reset
sim_run -stable
sim_save_reset

# Run check
if {$env(OPT_MODE) eq "gui"} {                            
        check_fv                                               
} else {                                                       
        check_fv -run_finish {report_fv -list > run/formal/${OPT_TOP}/results.txt; quit}
}
