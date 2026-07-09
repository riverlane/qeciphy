
# --- Device Configuration ---
set_global_assignment -name DEVICE_INITIALIZATION_CLOCK   OSC_CLK_1_125MHZ
set_global_assignment -name ACTIVE_SERIAL_CLOCK           AS_FREQ_100MHZ
set_global_assignment -name STRATIXV_CONFIGURATION_SCHEME "AVST X16"
set_global_assignment -name USE_CONF_DONE                 SDM_IO16

# --- Power Management (PMBus) ---
set_global_assignment -name VID_OPERATION_MODE            "PMBUS MASTER"
set_global_assignment -name USE_PWRMGT_SCL                SDM_IO0
set_global_assignment -name USE_PWRMGT_SDA                SDM_IO12
set_global_assignment -name PWRMGT_BUS_SPEED_MODE         "400 KHZ"
set_global_assignment -name NUMBER_OF_SLAVE_DEVICE        1
set_global_assignment -name PWRMGT_SLAVE_DEVICE_TYPE      OTHER
set_global_assignment -name PWRMGT_SLAVE_DEVICE0_ADDRESS  4F
set_global_assignment -name PWRMGT_PAGE_COMMAND_ENABLE    ON
set_global_assignment -name PWRMGT_VOLTAGE_OUTPUT_FORMAT  "LINEAR FORMAT"
set_global_assignment -name PWRMGT_LINEAR_FORMAT_N        "-12"

# --- EDA / Simulation ---
set_global_assignment -name EDA_SIMULATION_TOOL           "Questa Intel FPGA (Verilog)"

# --- Debug ---
set_global_assignment -name ENABLE_SIGNALTAP              ON

# --- Power Analysis ---
set_global_assignment -name POWER_APPLY_THERMAL_MARGIN    ADDITIONAL

# --- Transceiver ---
set_global_assignment -name PRESERVE_UNUSED_XCVR_CHANNEL  ON