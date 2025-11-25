
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_NULL_TEST_SEQ_SVH_
`define QECIPHY_NULL_TEST_SEQ_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_null_test_seq
//
// Abstract:
// Null test sequence - allows simulator to run but does nothing. Intended to check compilation.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_null_test_seq extends qeciphy_base_seq;

   `uvm_object_utils_begin(qeciphy_null_test_seq)
   `uvm_object_utils_end


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

      `uvm_info(msg_id, "Starting qeciphy_null_test_seq...", UVM_LOW)
      #1us;
      `uvm_info(msg_id, "Finished qeciphy_null_test_seq.", UVM_LOW)

   endtask: body
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_null_test_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_NULL_TEST_SEQ_SVH_
