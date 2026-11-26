# Usage: vivado -mode gui -source scripts/open_xvc_hw.tcl -tclargs <board_ip> <ltx_path>
set board_ip [lindex $argv 0]
set ltx_path [lindex $argv 1]

open_hw_manager
connect_hw_server -allow_non_jtag -cs_url TCP:localhost:3042

# Close existing XVC target if re-running
catch {close_hw_target}

# Connect to XVC server on port 2542 with retry loop
set connected 0
for {set i 0} {$i < 5} {incr i} {
    if {![catch {open_hw_target -xvc_url "${board_ip}:2542"}]} {
        set connected 1
        break
    }
    after 1000
}
if {!$connected} {
    error "Failed to connect to XVC server at ${board_ip}:2542"
}

# Assign .ltx probes and refresh debug cores
set hw_dev [lindex [get_hw_devices] 0]
current_hw_device $hw_dev
set_property PROBES.FILE $ltx_path $hw_dev
set_property FULL_PROBES.FILE $ltx_path $hw_dev
refresh_hw_device $hw_dev

# Open waveform viewer tabs for all detected ILA cores (and optional VIO dashboard)
set ilas [get_hw_ilas]
if {[llength $ilas] > 0} {
    foreach ila $ilas {
        display_hw_ila_data [upload_hw_ila_data $ila]
    }
    # Optional: automatically arm all ILAs on launch
    run_hw_ila $ilas
}

set vios [get_hw_vios]
if {[llength $vios] > 0} {
    display_hw_vio_data $vios
}
