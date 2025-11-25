
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_SMOKE_TEST_SVH_
`define QECIPHY_SMOKE_TEST_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_smoke_test
//
// Abstract:
// Test class for the Riverlane Limited qeciphy TB qeciphynull test.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_smoke_test extends qeciphy_base_test;

   // Control/status variables.

   `uvm_component_utils_begin(qeciphy_smoke_test)
   `uvm_component_utils_end


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function new (string name = "", uvm_component parent);
      super.new(name, parent);
   endfunction
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: run_main_test_sequence
   //
   // Create, randomize and execute the main test sequence.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_main_test_sequence();
      const string           msg_id = { get_type_name(), ".run_main_test_sequence" };
      int                    rand_ok;
      qeciphy_txrx_test_seq  test_seq;

      test_seq = qeciphy_txrx_test_seq::type_id::create("test_seq", .contxt(get_full_name()));
      rand_ok = test_seq.randomize() with {
         m_num_dut_xfers              == 1000;
         m_min_dut_delay_clks         == 0;
         m_max_dut_delay_clks         == 1;
         m_num_tbphy_xfers            == 1000;
         m_min_tbphy_delay_clks       == 0;
         m_max_tbphy_delay_clks       == 1;
      };
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize test_seq")
      test_seq.start(m_env.m_sequencer);

   endtask : run_main_test_sequence
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
endclass : qeciphy_smoke_test
//------------------------------------------------------------------------------------------------------------------------------------------

`endif // QECIPHY_SMOKE_TEST_SVH_

