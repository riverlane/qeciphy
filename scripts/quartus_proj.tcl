# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2026 Riverlane Ltd.
#
# quartus_proj_new.tcl — Dynamic Quartus project creation.
#
# Called from Makefile quartus_synth target via:
#   quartus_sh --script scripts/quartus_proj_new.tcl -tclargs \
#       <project_name> <device> <device_family> <top_level_entity> <variant> \
#       <line_rate_mbps> <rclk_freq_mhz> <constraints_list> [src_file ...]
#
# argv[0]  = project_name        e.g. qeciphy_integration
# argv[1]  = device              e.g. AGFB014R24B2E2V
# argv[2]  = device_family       e.g. Agilex 7
# argv[3]  = top_level_entity    e.g. qeciphy_syn_wrapper
# argv[4]  = variant             ETILE or FTILE
# argv[5]  = line_rate_mbps      e.g. 10312.5
# argv[6]  = rclk_freq_mhz       e.g. 156.25
# argv[7]  = constraints         space-separated list of .sdc/.tcl paths
# argv[8+] = source files        SRC_FILES and SYN_FILES

package require ::quartus::project

# ---------------------------------------------------------------------------
# Parse arguments
# ---------------------------------------------------------------------------
# quartus_sh --script puts the script path as argv[0]; strip it.
if {[llength $argv] > 0 && [string match "*tcl*" [lindex $argv 0]]} {
    set argv [lrange $argv 1 end]
}

if {[llength $argv] < 8} {
    puts "ERROR: quartus_proj_new.tcl requires at least 8 arguments."
    puts "  project_name device device_family top_level variant line_rate_mbps rclk_freq_mhz constraints [src_files...]"
    exit 1
}


puts "DEBUG: argv = $argv"

set proj_name      [lindex $argv 0]
set proj_device    [lindex $argv 1]
set device_family  [lindex $argv 2]
set top_entity     [lindex $argv 3]
set variant        [lindex $argv 4]
set line_rate_mbps [lindex $argv 5]
set rclk_freq_mhz  [lindex $argv 6]
set constraints    [lindex $argv 7]
set src_files      [lrange $argv 8 end]

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
# Variant exclusion — mirrors quartus_ip.tcl logic
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
# Create project directory structure
# ---------------------------------------------------------------------------
set start_dir  [pwd]
set vendor_dir [file join $start_dir "vendors" "altera" "25.3"]

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

    # IP file references — scan vendor dir, apply same exclusion as quartus_ip.tcl
    if {![file isdirectory $vendor_dir]} {
        puts "ERROR: Vendor directory not found: $vendor_dir"
        exit 1
    }
    set tcl_files [lsort [glob -nocomplain -directory $vendor_dir "*.tcl"]]
    if {[llength $tcl_files] == 0} {
        puts "WARNING: No .tcl files found in $vendor_dir — no IP_FILE assignments written."
    }
    foreach script_path $tcl_files {
        set script_name [file tail $script_path]
        if {[lsearch $excluded_scripts $script_name] >= 0} {
            continue
        }
        set ip_name "[file rootname $script_name].ip"
        set_global_assignment -name IP_FILE "ip/$ip_name"
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
	set_global_assignment -name ERROR_CHECK_FREQUENCY_DIVISOR 1
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
	set_instance_assignment -name RESERVE_PIN AS_BIDIRECTIONAL -to i2c_qsfpdd0_sda
	set_instance_assignment -name RESERVE_PIN AS_BIDIRECTIONAL -to i2c_qsfpdd0_scl
	set_instance_assignment -name IO_STANDARD "1.2 V" -to fpga_led[0] -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "1.2 V" -to fpga_led[1] -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "1.2 V" -to fpga_led[2] -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "1.2 V" -to fpga_led[3] -entity qeciphy_syn_wrapper
	set_instance_assignment -name XCVR_VCCR_VCCT_VOLTAGE 1_1V -to GT_TXP -entity qeciphy_syn_wrapper
	set_instance_assignment -name XCVR_VCCR_VCCT_VOLTAGE 1_1V -to GT_RXP -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD LVPECL -to gt_refclk_in_p -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "TRUE DIFFERENTIAL SIGNALING" -to clk_100_p -entity qeciphy_syn_wrapper
	set_instance_assignment -name INPUT_TERMINATION DIFFERENTIAL -to clk_100_p -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to GT_TXP -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to GT_RXP -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to GT_TXN -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to GT_RXN -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to GT_TXP_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to GT_RXP_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to GT_TXN_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to GT_RXN_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "1.2 V" -to i2c_qsfpdd0_scl -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "1.2 V" -to i2c_qsfpdd0_sda -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "1.2-V" -to qsfpdd0_modsel_L -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "1.2-V" -to qsfpdd0_reset_L -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "1.2-V" -to qsfpdd0_Initmode -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "1.2-V" -to qsfpdd0_modprs_L -entity qeciphy_syn_wrapper
	set_instance_assignment -name IO_STANDARD "1.2-V" -to qsfpdd0_int_L -entity qeciphy_syn_wrapper
	set_instance_assignment -name SLEW_RATE 1 -to qsfpdd0_modsel_L -entity qeciphy_syn_wrapper
	set_instance_assignment -name SLEW_RATE 1 -to qsfpdd0_reset_L -entity qeciphy_syn_wrapper
	set_instance_assignment -name SLEW_RATE 1 -to qsfpdd0_Initmode -entity qeciphy_syn_wrapper
	set_instance_assignment -name SLEW_RATE 1 -to i2c_qsfpdd0_sda -entity qeciphy_syn_wrapper
	set_instance_assignment -name SLEW_RATE 1 -to i2c_qsfpdd0_scl -entity qeciphy_syn_wrapper
	set_instance_assignment -name PARTITION_COLOUR 4294964852 -to qeciphy_dual_sim_top -entity qeciphy_syn_wrapper
	set_instance_assignment -name PARTITION_COLOUR 4294949993 -to auto_fab_0 -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "refclk_divider_enable_termination=enable_term" -to gt_refclk_in_p -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "refclk_divider_enable_3p3v=enable_3p3v_tol" -to gt_refclk_in_p -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "refclk_divider_input_freq=156250000" -to gt_refclk_in_p -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "refclk_divider_powerdown_mode=false" -to gt_refclk_in_p -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "refclk_divider_enable_hysteresis=disable_hyst" -to gt_refclk_in_p -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "txeq_main_tap=35" -to GT_TXP_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "txeq_pre_tap_1=5" -to GT_TXP_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "txeq_pre_tap_2=0" -to GT_TXP_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "txeq_post_tap_1=0" -to GT_TXP_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "rx_ac_couple_enable=ENABLE" -to GT_RXP_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "rx_onchip_termination=RXONCHIP_TERMINATION_R_2" -to GT_RXP_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "rx_term_mode_select=RXTERM_MODE_SELECT_GROUNDED" -to GT_RXP_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "refclk_divider_use_as_BTI_clock=TRUE" -to gt_refclk_in_p_1 -entity qeciphy_syn_wrapper
	set_instance_assignment -name HSSI_PARAMETER "refclk_divider_input_freq=156250000" -to gt_refclk_in_p_1 -entity qeciphy_syn_wrapper

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
puts "INFO: quartus_proj_new.tcl complete. Project: $proj_name"
