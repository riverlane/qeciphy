
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_POWER_UP_SEQ_SVH_
`define QECIPHY_POWER_UP_SEQ_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_power_up_seq
//
// Abstract:
// Power up the board.  The assumption is that resets will be active before clocks start but remain asserted until some time after.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_power_up_seq extends qeciphy_base_seq;

   // Control/status variables - not randomized.
   // HINT: Declare control fields here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   // Randomized variables.
   rand real m_dut_aclk_startup_delay_ns;
   rand real m_dut_rclk_startup_delay_ns;
   rand real m_dut_fclk_startup_delay_ns;
   rand real m_tbphy_aclk_startup_delay_ns;
   rand real m_tbphy_rclk_startup_delay_ns;
   rand real m_tbphy_fclk_startup_delay_ns;

   `uvm_object_utils_begin(qeciphy_power_up_seq)
      `uvm_field_real (m_dut_aclk_startup_delay_ns, UVM_DEFAULT)
      `uvm_field_real (m_dut_rclk_startup_delay_ns, UVM_DEFAULT)
      `uvm_field_real (m_dut_fclk_startup_delay_ns, UVM_DEFAULT)
      `uvm_field_real (m_tbphy_aclk_startup_delay_ns, UVM_DEFAULT)
      `uvm_field_real (m_tbphy_rclk_startup_delay_ns, UVM_DEFAULT)
      `uvm_field_real (m_tbphy_fclk_startup_delay_ns, UVM_DEFAULT)
   `uvm_object_utils_end

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //----------------------------------------------------------------------------------------------------------------------------------------
   constraint c_dut_aclk_startup_delay          {      m_dut_aclk_startup_delay_ns >=   0.0; }
   constraint c_moderate_dut_aclk_startup_delay { soft m_dut_aclk_startup_delay_ns <= 100.0; }

   constraint c_dut_rclk_startup_delay          {      m_dut_rclk_startup_delay_ns >=   0.0; }
   constraint c_moderate_dut_rclk_startup_delay { soft m_dut_rclk_startup_delay_ns <= 100.0; }

   constraint c_dut_fclk_startup_delay          {      m_dut_fclk_startup_delay_ns >=   0.0; }
   constraint c_moderate_dut_fclk_startup_delay { soft m_dut_fclk_startup_delay_ns <= 100.0; }

   constraint c_tbphy_aclk_startup_delay          {      m_tbphy_aclk_startup_delay_ns >=   0.0; }
   constraint c_moderate_tbphy_aclk_startup_delay { soft m_tbphy_aclk_startup_delay_ns <= 100.0; }

   constraint c_tbphy_rclk_startup_delay          {      m_tbphy_rclk_startup_delay_ns >=   0.0; }
   constraint c_moderate_tbphy_rclk_startup_delay { soft m_tbphy_rclk_startup_delay_ns <= 100.0; }

   constraint c_tbphy_fclk_startup_delay          {      m_tbphy_fclk_startup_delay_ns >=   0.0; }
   constraint c_moderate_tbphy_fclk_startup_delay { soft m_tbphy_fclk_startup_delay_ns <= 100.0; }
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

      // Configure all clocks to be the same as their master-clock.
      p_sequencer.m_config.m_vifs.dut_aclk_vif.set_divisor(0, 1);
      p_sequencer.m_config.m_vifs.dut_rclk_vif.set_divisor(0, 1);
      p_sequencer.m_config.m_vifs.dut_fclk_vif.set_divisor(0, 1);
      p_sequencer.m_config.m_vifs.tbphy_aclk_vif.set_divisor(0, 1);
      p_sequencer.m_config.m_vifs.tbphy_rclk_vif.set_divisor(0, 1);
      p_sequencer.m_config.m_vifs.tbphy_fclk_vif.set_divisor(0, 1);

      // Assert the reset and then wait for a bit before starting the clocks (spaced apart).
      p_sequencer.m_config.m_vifs.dut_aclk_vif.assert_reset(0);
      p_sequencer.m_config.m_vifs.tbphy_aclk_vif.assert_reset(0);
      fork
         begin
            #(m_dut_aclk_startup_delay_ns * 1.0ns);
            p_sequencer.m_config.m_vifs.dut_aclk_vif.set_master_period_ns(p_sequencer.m_config.m_dut_aclk_period_ns);
         end
         begin
            #(m_dut_rclk_startup_delay_ns * 1.0ns);
            p_sequencer.m_config.m_vifs.dut_rclk_vif.set_master_period_ns(p_sequencer.m_config.m_dut_rclk_period_ns);
         end
         begin
            #(m_dut_fclk_startup_delay_ns * 1.0ns);
            p_sequencer.m_config.m_vifs.dut_fclk_vif.set_master_period_ns(p_sequencer.m_config.m_dut_fclk_period_ns);
         end
         begin
            #(m_tbphy_aclk_startup_delay_ns * 1.0ns);
            p_sequencer.m_config.m_vifs.tbphy_aclk_vif.set_master_period_ns(p_sequencer.m_config.m_tbphy_aclk_period_ns);
         end
         begin
            #(m_tbphy_rclk_startup_delay_ns * 1.0ns);
            p_sequencer.m_config.m_vifs.tbphy_rclk_vif.set_master_period_ns(p_sequencer.m_config.m_tbphy_rclk_period_ns);
         end
         begin
            #(m_tbphy_fclk_startup_delay_ns * 1.0ns);
            p_sequencer.m_config.m_vifs.tbphy_fclk_vif.set_master_period_ns(p_sequencer.m_config.m_tbphy_fclk_period_ns);
         end
      join

   endtask: body
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_power_up_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_POWER_UP_SEQ_SVH_
