
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_POWER_DOWN_SEQ_SVH_
`define QECIPHY_POWER_DOWN_SEQ_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_power_down_seq
//
// Abstract:
// Stop all clocks and any other TB models. Do NOT change the state of any DUT pins - there is no defined state in power-down.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_power_down_seq extends qeciphy_base_seq;

   // Control/status variables - not randomized.
   // HINT: Declare control fields here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   // Randomized variables.
   // HINT: Declare randomizable variables here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   `uvm_object_utils_begin(qeciphy_power_down_seq)
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

   endtask: body
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_power_down_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_POWER_DOWN_SEQ_SVH_
