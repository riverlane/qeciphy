
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_RESET_SEQ_SVH_
`define QECIPHY_RESET_SEQ_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_reset_seq
//
// Abstract:
// Perform a hard reset on the DUT for the number of aclk periods given by the m_length_clks field.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_reset_seq extends qeciphy_base_seq;

   // Control/status variables - not randomized.
   // HINT: Declare control fields here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   // Randomized variables.
   rand int m_length_clks;

   `uvm_object_utils_begin(qeciphy_reset_seq)
      `uvm_field_int (m_length_clks, UVM_DEFAULT | UVM_DEC)
   `uvm_object_utils_end

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //----------------------------------------------------------------------------------------------------------------------------------------
   constraint c_valid_length    {      m_length_clks >= 16; }
   constraint c_moderate_length { soft m_length_clks < 100; }
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

      // Assert both resets and hold for the required number of ACLKs.
      fork
         begin
            p_sequencer.m_config.m_vifs.dut_aclk_vif.assert_reset(0);
            repeat(m_length_clks) @(posedge p_sequencer.m_config.m_vifs.dut_aclk_vif.clks[0]);
            p_sequencer.m_config.m_vifs.dut_aclk_vif.release_reset(0);
         end
         begin
            p_sequencer.m_config.m_vifs.tbphy_aclk_vif.assert_reset(0);
            repeat(m_length_clks) @(posedge p_sequencer.m_config.m_vifs.tbphy_aclk_vif.clks[0]);
            p_sequencer.m_config.m_vifs.tbphy_aclk_vif.release_reset(0);
         end
      join

   endtask: body
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_reset_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_RESET_SEQ_SVH_
