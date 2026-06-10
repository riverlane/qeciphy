# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2026 Riverlane Ltd.
#
# quartus_proj.tcl — Dynamic Quartus project creation.
#
# Called from Makefile quartus_synth target via:
#   quartus_sh --script scripts/quartus_proj.tcl -tclargs \
#       <top_level_entity> <constraints_list> <device> <device_family> <variant> \
#       <project_name> [src_file ...]
#
# argv[0]  = top_level_entity    e.g. qeciphy_syn_wrapper
# argv[1]  = constraints         space-separated list of .sdc/.tcl paths
# argv[2]  = device              e.g. AGFB014R24B2E2V
# argv[3]  = device_family       e.g. Agilex 7
# argv[4]  = variant             ETILE or FTILE
# argv[5]  = project_name        e.g. qeciphy_integration
# argv[6+] = source files        SRC_FILES and SYN_FILES

package require ::quartus::project

# ---------------------------------------------------------------------------
# Parse arguments
# ---------------------------------------------------------------------------
# quartus_sh --script puts the script path as argv[0]; strip it.
if {[llength $argv] > 0 && [string match "*tcl*" [lindex $argv 0]]} {
    set argv [lrange $argv 1 end]
}

if {[llength $argv] < 6} {
    puts "ERROR: quartus_proj.tcl requires at least 6 arguments."
    puts "  top_level constraints device device_family variant project_name [src_files...]"
    exit 1
}

set top_entity     [lindex $argv 0]
set constraints    [lindex $argv 1]
set proj_device    [lindex $argv 2]
set device_family  [lindex $argv 3]
set variant        [lindex $argv 4]
set proj_name      [lindex $argv 5]
set src_files      [lrange $argv 6 end]

# ---------------------------------------------------------------------------
# File type classification
# ---------------------------------------------------------------------------
proc get_file_assignment {filepath} {
    set ext [string tolower [file extension $filepath]]
    switch -- $ext {
        ".sv"            { return "SYSTEMVERILOG_FILE" }
        ".v"             { return "VERILOG_FILE" }
        ".vhd" - ".vhdl" { return "VHDL_FILE" }
        ".sdc" - ".tcl"  { return "SDC_FILE" }
        ".ip"            { return "IP_FILE" }
        ".qip"           { return "QIP_FILE" }
        default          { return "" }
    }
}

# ---------------------------------------------------------------------------
# Create project directory structure
# ---------------------------------------------------------------------------
set start_dir  [pwd]

set target_dir [file normalize [file join $start_dir "run"]]
if {![file isdirectory $target_dir]} {
    file mkdir $target_dir
    puts "INFO: Created run directory: $target_dir"
}

set proj_dir [file join $target_dir $proj_name]
if {![file isdirectory $proj_dir]} {
    file mkdir $proj_dir
    puts "INFO: Created project directory: $proj_dir"
}

# Create ip/ subdirectory so IP_FILE refs resolve after quartus_ip.tcl runs
file mkdir [file join $proj_dir "ip"]

cd $proj_dir
puts "INFO: Working in project directory: [pwd]"

# ---------------------------------------------------------------------------
# Open or create project
# ---------------------------------------------------------------------------
set need_to_close_project 0
set make_assignments 1

if {[is_project_open]} {
    if {[string compare $quartus(project) $proj_name] != 0} {
        puts "WARNING: A different project is open. Skipping assignments."
        set make_assignments 0
    }
} else {
    if {[project_exists $proj_name]} {
        project_open -revision $proj_name $proj_name
    } else {
        project_new -revision $proj_name $proj_name
    }
    set need_to_close_project 1
}
cd ../../
if {$make_assignments} {

    # Static project settings
    
	set_global_assignment -name ORIGINAL_QUARTUS_VERSION 25.3.1
    set_global_assignment -name LAST_QUARTUS_VERSION         "25.3.1 Pro Edition"
    set_global_assignment -name PROJECT_OUTPUT_DIRECTORY     output_files
    set_global_assignment -name FAMILY                       $device_family
    set_global_assignment -name DEVICE                       $proj_device
    set_global_assignment -name DEVICE_INITIALIZATION_CLOCK  OSC_CLK_1_125MHZ
    set_global_assignment -name TOP_LEVEL_ENTITY             $top_entity
    set_global_assignment -name VERILOG_INPUT_VERSION        SYSTEMVERILOG_2012
    set_global_assignment -name VHDL_INPUT_VERSION           VHDL_2019
    set_global_assignment -name FLOW_DISABLE_ASSEMBLER       OFF
    set_global_assignment -name PROJECT_IP_REGENERATION_POLICY ALWAYS_REGENERATE_IP
    set_global_assignment -name ERROR_CHECK_FREQUENCY_DIVISOR 1
    set_global_assignment -name BOARD                        default
    set_global_assignment -name GENERATE_PROGRAMMING_FILES ON

    # Source files — classified by extension
    foreach f $src_files {
        set assignment [get_file_assignment $f]
        if {$assignment ne ""} {
            set_global_assignment -name $assignment ../../$f
        } else {
            puts "WARNING: Unrecognised file extension, skipping: $f"
        }
    }

    # Constraint files — .sdc files are added as SDC_FILE references;
    # .tcl files contain Quartus assignment commands and are sourced directly.
    foreach cfile $constraints {
        if {$cfile eq ""} { continue }
        set ext [string tolower [file extension $cfile]]
        if {$ext eq ".tcl"} {
            puts "INFO: Sourcing constraint script: $cfile"
            source $cfile
        } elseif {$ext eq ".stp"} {
    	    set_global_assignment -name USE_SIGNALTAP_FILE ../../$cfile
    	    set_global_assignment -name SIGNALTAP_FILE ../../$cfile
        } else {
            set_global_assignment -name SDC_FILE ../../$cfile
        }
    }

    # Auto-tiles support logic (if present from previous run)
    set spd_file "support_logic/${proj_name}_auto_tiles.spd"
    set qip_file "support_logic/${proj_name}_auto_tiles.qip"
    if {[file exists $spd_file]} {
        set_global_assignment -name SPD_FILE $spd_file -tag quartus_tlg
    }
    if {[file exists $qip_file]} {
        set_global_assignment -name QIP_FILE $qip_file \
            -comment "Order-dependent: must appear after all other QIP_FILE and IP_FILE settings" \
            -tag quartus_tlg
    }
	set_global_assignment -name VID_OPERATION_MODE "PMBUS MASTER"
	set_global_assignment -name USE_PWRMGT_SCL SDM_IO0
	set_global_assignment -name USE_PWRMGT_SDA SDM_IO12
	set_global_assignment -name USE_CONF_DONE SDM_IO16
	set_global_assignment -name ACTIVE_SERIAL_CLOCK AS_FREQ_100MHZ
	set_global_assignment -name STRATIXV_CONFIGURATION_SCHEME "AVST X16"
	set_global_assignment -name EDA_SIMULATION_TOOL "Questa Intel FPGA (Verilog)"
	set_global_assignment -name PWRMGT_BUS_SPEED_MODE "400 KHZ"
	set_global_assignment -name PWRMGT_SLAVE_DEVICE_TYPE OTHER
	set_global_assignment -name PWRMGT_SLAVE_DEVICE0_ADDRESS 4F
	set_global_assignment -name PWRMGT_PAGE_COMMAND_ENABLE ON
	set_global_assignment -name NUMBER_OF_SLAVE_DEVICE 1
	set_global_assignment -name PWRMGT_VOLTAGE_OUTPUT_FORMAT "LINEAR FORMAT"
	set_global_assignment -name PWRMGT_LINEAR_FORMAT_N "-12"
	set_global_assignment -name ENABLE_SIGNALTAP ON
	set_global_assignment -name POWER_APPLY_THERMAL_MARGIN ADDITIONAL
    set_global_assignment -name PRESERVE_UNUSED_XCVR_CHANNEL ON
    
	# set_instance_assignment -name PARTITION_COLOUR 4294964852 -to qeciphy_dual_sim_top -entity qeciphy_syn_wrapper
	# set_instance_assignment -name PARTITION_COLOUR 4294949993 -to auto_fab_0 -entity qeciphy_syn_wrapper
	# set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to gt_tx_p_1 -entity qeciphy_syn_wrapper
	# set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to gt_rx_p_1 -entity qeciphy_syn_wrapper
	# set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to gt_tx_n_1 -entity qeciphy_syn_wrapper
	# set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to gt_rx_n_1 -entity qeciphy_syn_wrapper

    export_assignments
    puts "INFO: Project assignments written for '$proj_name'."
}

# ---------------------------------------------------------------------------
# Close project and return
# ---------------------------------------------------------------------------
if {$need_to_close_project} {
    project_close
}

cd $start_dir
puts "INFO: quartus_proj.tcl complete. Project: $proj_name"
