
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_NULL_TEST_SVH_
`define QECIPHY_NULL_TEST_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_null_test
//
// Abstract:
// Test class for the Riverlane Limited qeciphy TB qeciphynull test.
// Null test - allows simulator to run but does nothing. Intended to check compilation.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_null_test extends qeciphy_base_test;

   `uvm_component_utils_begin(qeciphy_null_test)
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
      qeciphy_null_test_seq  test_seq;

      test_seq = qeciphy_null_test_seq::type_id::create("test_seq", .contxt(get_full_name()));
      if (! test_seq.randomize()) `uvm_fatal(msg_id, "Failed to randomize test_seq")
      test_seq.start(m_env.m_sequencer);

   endtask : run_main_test_sequence
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
endclass : qeciphy_null_test
//------------------------------------------------------------------------------------------------------------------------------------------

`endif // QECIPHY_NULL_TEST_SVH_

