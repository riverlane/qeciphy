# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2024-2026 Riverlane Ltd.
# Original authors: Evan Sun

#CLOCKS

set_location_assignment PIN_JD74 -to gt_refclk_in_p
set_location_assignment PIN_N45 -to clk_100_p

set_instance_assignment -name IO_STANDARD "TRUE DIFFERENTIAL SIGNALING" -to clk_100_p -entity qeciphy_syn_wrapper
set_instance_assignment -name INPUT_TERMINATION DIFFERENTIAL -to clk_100_p -entity qeciphy_syn_wrapper

#Transceivers

set_location_assignment PIN_MB71 -to gt_tx_p
set_location_assignment PIN_ME69 -to gt_tx_n
set_location_assignment PIN_MB77 -to gt_rx_p
set_location_assignment PIN_ME76 -to gt_rx_n

set_instance_assignment -name IO_STANDARD "CURRENT MODE LOGIC (CML)" -to gt_refclk_in_p -entity qeciphy_syn_wrapper


set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to gt_tx_p -entity qeciphy_syn_wrapper
set_instance_assignment -name HSSI_PARAMETER "txeq_main_tap=35" -to gt_tx_p -entity qeciphy_syn_wrapper
set_instance_assignment -name HSSI_PARAMETER "txeq_pre_tap_1=5" -to gt_tx_p -entity qeciphy_syn_wrapper
set_instance_assignment -name HSSI_PARAMETER "txeq_pre_tap_2=0" -to gt_tx_p -entity qeciphy_syn_wrapper
set_instance_assignment -name HSSI_PARAMETER "txeq_post_tap_1=0" -to gt_tx_p -entity qeciphy_syn_wrapper

set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to gt_tx_n -entity qeciphy_syn_wrapper


set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to gt_rx_p -entity qeciphy_syn_wrapper
set_instance_assignment -name HSSI_PARAMETER "rx_ac_couple_enable=ENABLE" -to gt_rx_p -entity qeciphy_syn_wrapper
set_instance_assignment -name HSSI_PARAMETER "rx_onchip_termination=RX_ONCHIP_TERMINATION_R_2" -to gt_rx_p -entity qeciphy_syn_wrapper
set_instance_assignment -name HSSI_PARAMETER "rx_term_mode_select=RX_TERM_MODE_SELECT_GROUNDED" -to gt_rx_p -entity qeciphy_syn_wrapper
set_instance_assignment -name IO_STANDARD "HIGH SPEED DIFFERENTIAL I/O" -to gt_rx_n -entity qeciphy_syn_wrapper

#Other IO

set_location_assignment PIN_H46 -to fpga_led[0]
set_location_assignment PIN_J45 -to fpga_led[1]
set_location_assignment PIN_D46 -to fpga_led[2]
set_location_assignment PIN_B45 -to fpga_led[3]

set_instance_assignment -name IO_STANDARD "1.2 V" -to fpga_led[0] -entity qeciphy_syn_wrapper
set_instance_assignment -name IO_STANDARD "1.2 V" -to fpga_led[1] -entity qeciphy_syn_wrapper
set_instance_assignment -name IO_STANDARD "1.2 V" -to fpga_led[2] -entity qeciphy_syn_wrapper
set_instance_assignment -name IO_STANDARD "1.2 V" -to fpga_led[3] -entity qeciphy_syn_wrapper


set_location_assignment PIN_KJ61 -to i2c_qsfpdd0_scl
set_location_assignment PIN_KF60 -to i2c_qsfpdd0_sda

set_instance_assignment -name RESERVE_PIN AS_BIDIRECTIONAL -to i2c_qsfpdd0_sda
set_instance_assignment -name RESERVE_PIN AS_BIDIRECTIONAL -to i2c_qsfpdd0_scl
set_instance_assignment -name IO_STANDARD "1.2 V" -to i2c_qsfpdd0_scl -entity qeciphy_syn_wrapper
set_instance_assignment -name IO_STANDARD "1.2 V" -to i2c_qsfpdd0_sda -entity qeciphy_syn_wrapper
set_instance_assignment -name SLEW_RATE 1 -to i2c_qsfpdd0_sda -entity qeciphy_syn_wrapper
set_instance_assignment -name SLEW_RATE 1 -to i2c_qsfpdd0_scl -entity qeciphy_syn_wrapper


#Optional QSFPDD control signals - not required for basic operation, but may be needed for some use cases
#set_location_assignment PIN_CM23 -to qsfpdd0_reset_L
#set_location_assignment PIN_CR24 -to qsfpdd0_modprs_L
#set_location_assignment PIN_CP23 -to qsfpdd0_Initmode
#set_location_assignment PIN_CL24 -to qsfpdd0_modsel_L
# set_instance_assignment -name IO_STANDARD "1.2-V" -to qsfpdd0_modsel_L -entity qeciphy_syn_wrapper
# set_instance_assignment -name IO_STANDARD "1.2-V" -to qsfpdd0_reset_L -entity qeciphy_syn_wrapper
# set_instance_assignment -name IO_STANDARD "1.2-V" -to qsfpdd0_Initmode -entity qeciphy_syn_wrapper
# set_instance_assignment -name IO_STANDARD "1.2-V" -to qsfpdd0_modprs_L -entity qeciphy_syn_wrapper
# set_instance_assignment -name IO_STANDARD "1.2-V" -to qsfpdd0_int_L -entity qeciphy_syn_wrapper
# set_instance_assignment -name SLEW_RATE 1 -to qsfpdd0_modsel_L -entity qeciphy_syn_wrapper
# set_instance_assignment -name SLEW_RATE 1 -to qsfpdd0_reset_L -entity qeciphy_syn_wrapper
# set_instance_assignment -name SLEW_RATE 1 -to qsfpdd0_Initmode -entity qeciphy_syn_wrapper