
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_ENV_CONFIG_SVH_
`define QECIPHY_ENV_CONFIG_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_env_config
//
// Abstract:
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_env_config extends uvm_object;

   // Control/status variables - not randomized.
   bit                      m_enable_ral          = 1;           // 1/0 = Enable/disable use of UVM RAL models.
   bit                      m_enable_scoreboards  = 1;           // 1/0 = Enable/disable all scoreboards/checkers.
   bit                      m_enable_coverage     = 1;           // 1/0 = Enable/disable all coverage collectors.
   uvm_active_passive_enum  m_is_active           = UVM_ACTIVE;  // Environment agents may be active or all of them are forced to be passive.

   // Randomized variables.
   rand real m_dut_aclk_period_ns;
   rand real m_dut_fclk_period_ns;
   rand real m_dut_rclk_period_ns;
   rand real m_tbphy_aclk_period_ns;
   rand real m_tbphy_fclk_period_ns;
   rand real m_tbphy_rclk_period_ns;

   `uvm_object_utils_begin(qeciphy_env_config)
      `uvm_field_int  (m_enable_ral,                         UVM_DEFAULT | UVM_BIN)
      `uvm_field_int  (m_enable_scoreboards,                 UVM_DEFAULT | UVM_BIN)
      `uvm_field_int  (m_enable_coverage,                    UVM_DEFAULT | UVM_BIN)
      `uvm_field_enum (uvm_active_passive_enum, m_is_active, UVM_DEFAULT          )
      `uvm_field_real (m_dut_aclk_period_ns,                 UVM_DEFAULT          )
      `uvm_field_real (m_dut_fclk_period_ns,                 UVM_DEFAULT          )
      `uvm_field_real (m_dut_rclk_period_ns,                 UVM_DEFAULT          )
      `uvm_field_real (m_tbphy_aclk_period_ns,               UVM_DEFAULT          )
      `uvm_field_real (m_tbphy_fclk_period_ns,               UVM_DEFAULT          )
      `uvm_field_real (m_tbphy_rclk_period_ns,               UVM_DEFAULT          )
   `uvm_object_utils_end

   // Virtual interfaces for each agent (fetched from ConfigDB and applied to associated agents).
   t_qeciphy_env_vifs  m_vifs;

   // UVM RAL register block used by this environment
   uvm_reg_block  m_regs;

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //----------------------------------------------------------------------------------------------------------------------------------------
   constraint c_moderate_dut_aclk_period   { soft m_dut_aclk_period_ns   >= 1.0; soft m_dut_aclk_period_ns   <= 100.0; }
   constraint c_moderate_dut_rclk_period   { soft m_dut_rclk_period_ns   >= 1.0; soft m_dut_rclk_period_ns   <= 100.0; }
   constraint c_moderate_dut_fclk_period   { soft m_dut_fclk_period_ns   >= 1.0; soft m_dut_fclk_period_ns   <= 100.0; }
   constraint c_moderate_tbphy_aclk_period { soft m_tbphy_aclk_period_ns >= 1.0; soft m_tbphy_aclk_period_ns <= 100.0; }
   constraint c_moderate_tbphy_rclk_period { soft m_tbphy_rclk_period_ns >= 1.0; soft m_tbphy_rclk_period_ns <= 100.0; }
   constraint c_moderate_tbphy_fclk_period { soft m_tbphy_fclk_period_ns >= 1.0; soft m_tbphy_fclk_period_ns <= 100.0; }
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function new(string name = "");
      super.new(name);
   endfunction : new
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: set_default_config
   //
   // Set some default values that can be used when creating default configurations.
   // Overriding this in extended classes can allow factory overrides to use different defaults.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void set_default_config();
      m_enable_coverage    = 1'b1;
      m_enable_scoreboards = 1'b1;
      m_is_active          = UVM_ACTIVE;
   endfunction: set_default_config
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: set_passive
   //
   // Ensure that all agents will operate as a passive agents (not driving interface signals).
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void set_passive();
      m_is_active = UVM_PASSIVE;
   endfunction: set_passive
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_env_config
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_ENV_CONFIG_SVH_
