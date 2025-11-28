
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_RESET_TEST_SEQ_SVH_
`define QECIPHY_RESET_TEST_SEQ_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_reset_test_seq
//
// Abstract:
// Randomly cycles the DUT between low- and active-power states.
// Cycles can be initiated by the DUT or the TB-Phy, but only one can initiate them at a time.
// See the field descriptions below for details of how to constrain the sequence.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_reset_test_seq extends qeciphy_power_state_test_seq;

    `uvm_object_utils(qeciphy_reset_test_seq)

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
   // Task: set_power_state
   //
   // Set the state of the required device to either low-power (state = 0) or active (state = 1).
   // NOTE: QECi-Phy uses synchronous P-Channel, so align with clocks.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task set_power_state (string target, bit state);
      const string                       msg_id = { get_type_name(), ".power_state_cycle" };
      riv_pbus_controller_sequencer      seqr;
      riv_pbus_controller_set_state_seq  set_state_seq;
      qeciphy_reset_seq                  reset_seq;
      int                                rand_ok;
      real                               aclk_prd_ns;

      // Select required sequencer and ACLK period then wait for next appropriate rising clock edge.
      case (target)
         "DUT"    :  begin
                        seqr        = p_sequencer.m_dut_pbus_seqr;
                        aclk_prd_ns = p_sequencer.m_config.m_dut_aclk_period_ns;
                        @(posedge p_sequencer.m_config.m_vifs.miscio_vif.dut_aclk);
                     end
         "TB-Phy" :  begin
                        seqr        = p_sequencer.m_tbphy_pbus_seqr;
                        aclk_prd_ns = p_sequencer.m_config.m_tbphy_aclk_period_ns;
                        @(posedge p_sequencer.m_config.m_vifs.miscio_vif.tbphy_aclk);
                     end
         default  : `uvm_fatal(msg_id, $sformatf("Bad target: %0s", target))
      endcase

      // Initiate a power-change with timings randomly distributed to cover < 1 ACLK, 1-2 ACLKs and > 2 ACLKs to test synchronizing).
      `uvm_info(msg_id, $sformatf("%0s requesting %0s state...", target, (state == 1'b0) ? "low-power" : "active"), UVM_LOW)
      set_state_seq = riv_pbus_controller_set_state_seq::type_id::create("set_state_seq", .contxt(get_full_name()));
      reset_seq = qeciphy_reset_seq::type_id::create("reset_seq", .contxt(get_full_name()));
         if (! reset_seq.randomize()) `uvm_fatal(msg_id, "Failed to randomize reset_seq")
         
      rand_ok = set_state_seq.randomize() with {
         new_state == state;
         tsu_state2req_ns  dist  {
                                    [0.1 : (aclk_prd_ns - 0.1)]                                 :/ 1,
                                    [((aclk_prd_ns * 1.0) + 0.1) : ((aclk_prd_ns * 2.0) - 0.1)] :/ 1,
                                    [((aclk_prd_ns * 2.0) + 0.1) : ((aclk_prd_ns * 9.0) - 0.1)] :/ 1
                                 };
         th_req2state_ns   dist  {
                                    [0.1 : (aclk_prd_ns - 0.1)]                                 :/ 1,
                                    [((aclk_prd_ns * 1.0) + 0.1) : ((aclk_prd_ns * 2.0) - 0.1)] :/ 1,
                                    [((aclk_prd_ns * 2.0) + 0.1) : ((aclk_prd_ns * 9.0) - 0.1)] :/ 1
                                 };
         tpd_accept2req_ns dist  {
                                    [0.1 : (aclk_prd_ns - 0.1)]                                 :/ 1,
                                    [((aclk_prd_ns * 1.0) + 0.1) : ((aclk_prd_ns * 2.0) - 0.1)] :/ 1,
                                    [((aclk_prd_ns * 2.0) + 0.1) : ((aclk_prd_ns * 9.0) - 0.1)] :/ 1
                                 };
      };
      fork
         set_state_seq.start(seqr, this);
         reset_seq.start(p_sequencer);
      join

   endtask: set_power_state
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_reset_test_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_RESET_TEST_SEQ_SVH_