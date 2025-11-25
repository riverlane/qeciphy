
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_SLEEP_TO_RESET_TEST_SEQ_SVH_
`define QECIPHY_SLEEP_TO_RESET_TEST_SEQ_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_sleep_to_reset_test_seq
//
// Abstract:
// Randomly cycles the DUT between low- and active-power states.
// Cycles can be initiated by the DUT or the TB-Phy, but only one can initiate them at a time.
// See the field descriptions below for details of how to constrain the sequence.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_sleep_to_reset_test_seq extends qeciphy_power_state_test_seq;

 `uvm_object_utils(qeciphy_sleep_to_reset_test_seq)

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
   // Task: power_state_cycle
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task power_state_cycle (string target, int duration_ns);
      const string                       msg_id = { get_type_name(), ".power_state_cycle" };
      qeciphy_wait_link_ready_seq        wait_link_ready_seq;
      qeciphy_reset_seq                  reset_seq;
      int                                rand_ok;
     
     reset_seq = qeciphy_reset_seq::type_id::create("reset_seq", .contxt(get_full_name()));
         if (! reset_seq.randomize()) `uvm_fatal(msg_id, "Failed to randomize reset_seq")
      // Initiate a power-down, wait for required duration then power up.
      set_power_state(target, 0);
      #SLEEP_TIME reset_seq.start(p_sequencer);
      #(duration_ns * 1.0ns);
      set_power_state(target, 1);
      

      
      // Wait until LINK is up
      `uvm_do_with(wait_link_ready_seq, { m_timeout_us == 100_000.0; })

   endtask: power_state_cycle
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_sleep_to_reset_test_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_SLEEP_TO_RESET_TEST_SEQ_SVH_