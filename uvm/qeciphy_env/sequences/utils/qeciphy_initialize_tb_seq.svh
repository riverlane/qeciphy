
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_INITIALIZE_TB_SEQ_SVH_
`define QECIPHY_INITIALIZE_TB_SEQ_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_initialize_tb_seq
//
// Abstract:
// Initialize the TB and any models in it. Only intended for use at start of simulation.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_initialize_tb_seq extends qeciphy_base_seq;

   // Control/status variables - not randomized.
   // HINT: Declare control fields here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   // Randomized variables.
   // HINT: Declare randomizable variables here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   `uvm_object_utils_begin(qeciphy_initialize_tb_seq)
   `uvm_object_utils_end

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //----------------------------------------------------------------------------------------------------------------------------------------
   // HINT: Add constraints here.
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
   // Task: body
   //
   // Disable all clock generators but make sure they are active.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task body ();
      const string msg_id = { get_type_name(), ".body" };

      // Disable all clocks
      p_sequencer.m_config.m_vifs.dut_aclk_vif.set_master_period_ns(0.0);
      p_sequencer.m_config.m_vifs.dut_rclk_vif.set_master_period_ns(0.0);
      p_sequencer.m_config.m_vifs.dut_fclk_vif.set_master_period_ns(0.0);
      p_sequencer.m_config.m_vifs.tbphy_aclk_vif.set_master_period_ns(0.0);
      p_sequencer.m_config.m_vifs.tbphy_rclk_vif.set_master_period_ns(0.0);
      p_sequencer.m_config.m_vifs.tbphy_fclk_vif.set_master_period_ns(0.0);

      // DUT uses active-low resets.  Only the ACLK domain has a reset.
      p_sequencer.m_config.m_vifs.dut_aclk_vif.set_reset_level(0, 1'b0);
      p_sequencer.m_config.m_vifs.tbphy_aclk_vif.set_reset_level(0, 1'b0);

      // We're running sequences in the environment so clock generators need to be active.
      p_sequencer.m_config.m_vifs.dut_aclk_vif.set_active();
      p_sequencer.m_config.m_vifs.dut_rclk_vif.set_active();
      p_sequencer.m_config.m_vifs.dut_fclk_vif.set_active();
      p_sequencer.m_config.m_vifs.tbphy_aclk_vif.set_active();
      p_sequencer.m_config.m_vifs.tbphy_rclk_vif.set_active();
      p_sequencer.m_config.m_vifs.tbphy_fclk_vif.set_active();

      // We're running sequences in the environment so dut <-> tbphy connectors need to be active.
      p_sequencer.m_config.m_vifs.dut2tbphy_conn_vif.set_active();
      p_sequencer.m_config.m_vifs.tbphy2dut_conn_vif.set_active();

   endtask: body
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_initialize_tb_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_INITIALIZE_TB_SEQ_SVH_
