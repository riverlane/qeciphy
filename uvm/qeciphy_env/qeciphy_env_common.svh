//------------------------------------------------------------------------------------------------------------------------------------------
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_ENV_COMMON_SVH_
`define QECIPHY_ENV_COMMON_SVH_



// Typedefs, constants, functions and tasks for use within the qeciphy_env_pkg package.
//------------------------------------------------------------------------------------------------------------------------------------------

// Package-wide implementation classes for agent analysis ports.
`uvm_analysis_imp_decl(_axis_sink_ap)
`uvm_analysis_imp_decl(_axis_source_ap)
`uvm_analysis_imp_decl(_dut_pbus_ap)
`uvm_analysis_imp_decl(_tbphy_pbus_ap)
`uvm_analysis_imp_decl(_dut_pbus_start_ap)
`uvm_analysis_imp_decl(_tbphy_pbus_start_ap)

// Structure to hold all virtual interfaces used by the environment.
typedef struct {
   virtual qeciphy_env_miscio_if           miscio_vif;
   virtual riv_clk_rst_gen_vip_if          dut_aclk_vif;
   virtual riv_clk_rst_gen_vip_if          dut_rclk_vif;
   virtual riv_clk_rst_gen_vip_if          dut_fclk_vif;
   virtual riv_pbus_controller_agent_if    dut_pbus_vif;
   virtual riv_rdy_vld_sink_agent_if       dut_axis_rx_vif;
   virtual riv_rdy_vld_source_agent_if     dut_axis_tx_vif;
   virtual riv_clk_rst_gen_vip_if          tbphy_aclk_vif;
   virtual riv_clk_rst_gen_vip_if          tbphy_rclk_vif;
   virtual riv_clk_rst_gen_vip_if          tbphy_fclk_vif;
   virtual riv_pbus_controller_agent_if    tbphy_pbus_vif;
   virtual riv_rdy_vld_sink_agent_if       tbphy_axis_rx_vif;
   virtual riv_rdy_vld_source_agent_if     tbphy_axis_tx_vif;
   virtual riv_diff_pair_connector_vip_if  dut2tbphy_conn_vif;
   virtual riv_diff_pair_connector_vip_if  tbphy2dut_conn_vif;
} t_qeciphy_env_vifs;

typedef enum logic[3:0] {
   PHY_RESET              = 4'h0,
   PHY_WAIT_FOR_RESET     = 4'h1,
   PHY_LINK_TRAINING      = 4'h2,
   PHY_RX_LOCKED          = 4'h3,
   PHY_LINK_READY         = 4'h4,
   PHY_FAULT_FATAL        = 4'h5,
   PHY_SLEEP              = 4'h6,
   PHY_WAIT_FOR_POWERDOWN = 4'h7
} qeciphy_state_enum;
const qeciphy_state_enum all_qeciphy_states[] = '{
   PHY_RESET, PHY_WAIT_FOR_RESET, PHY_LINK_TRAINING, PHY_RX_LOCKED, PHY_LINK_READY, PHY_FAULT_FATAL, PHY_SLEEP, PHY_WAIT_FOR_POWERDOWN
};

typedef enum logic[3:0] {
   PHY_OK          = 4'h0,
   PHY_FAP_MISSING = 4'h1,
   PHY_CRC_ERROR   = 4'h2
} qeciphy_error_enum;
const qeciphy_error_enum all_qeciphy_errors[] = '{PHY_OK, PHY_FAP_MISSING, PHY_CRC_ERROR};
localparam SLEEP_TIME = 10343ns;
`endif  // QECIPHY_ENV_COMMON_SVH_
