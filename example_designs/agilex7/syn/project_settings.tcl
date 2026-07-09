# --- Device Configuration ---
set_global_assignment -name DEVICE_INITIALIZATION_CLOCK   OSC_CLK_1_125MHZ
set_global_assignment -name ACTIVE_SERIAL_CLOCK           AS_FREQ_100MHZ
set_global_assignment -name STRATIXV_CONFIGURATION_SCHEME "AVST X8"
set_global_assignment -name USE_CONF_DONE                 SDM_IO16

# --- Power Management (PMBus) ---
set_global_assignment -name VID_OPERATION_MODE            "PMBUS MASTER"
set_global_assignment -name USE_PWRMGT_SCL                SDM_IO0
set_global_assignment -name USE_PWRMGT_SDA                SDM_IO12
set_global_assignment -name PWRMGT_BUS_SPEED_MODE         "100 KHZ"
set_global_assignment -name PWRMGT_SLAVE_DEVICE_TYPE      OTHER
set_global_assignment -name PWRMGT_SLAVE_DEVICE0_ADDRESS  47
set_global_assignment -name PWRMGT_SLAVE_DEVICE1_ADDRESS  00
set_global_assignment -name PWRMGT_SLAVE_DEVICE2_ADDRESS  00
set_global_assignment -name PWRMGT_PAGE_COMMAND_ENABLE    OFF
set_global_assignment -name PWRMGT_VOLTAGE_OUTPUT_FORMAT  "LINEAR FORMAT"
set_global_assignment -name PWRMGT_LINEAR_FORMAT_N        "-12"
set_global_assignment -name PWRMGT_TRANSLATED_VOLTAGE_VALUE_UNIT VOLTS

# --- EDA / Simulation ---
set_global_assignment -name EDA_SIMULATION_TOOL           "Questa Intel FPGA (Verilog)"

# --- Synthesis ---
set_global_assignment -name FAST_PRESERVE                 OFF -entity qeciphy_syn_wrapper
set_global_assignment -name GENERATE_COMPRESSED_SOF       ON

# --- Debug ---
set_global_assignment -name ENABLE_SIGNALTAP              ON

# --- Power Analysis ---
set_global_assignment -name POWER_APPLY_THERMAL_MARGIN    ADDITIONAL

# --- Transceiver ---