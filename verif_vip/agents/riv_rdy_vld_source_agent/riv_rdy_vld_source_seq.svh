
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SOURCE_SEQ_SVH_
`define RIV_RDY_VLD_SOURCE_SEQ_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_source_seq
//
// This is the base sequence class from which all dummy sequences should be extended.
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_source_seq extends uvm_sequence#(.REQ(riv_rdy_vld_source_txn), .RSP(riv_rdy_vld_source_txn));

   // Control/status variables - not randomized.
   // HINT: Declare control fields here (use m_ prefix) and also add them to the `uvm_object_utils_begin below.

   // Randomized variables.
   // HINT: Declare randomizable variables here (use m_ prefix) and also add them to the `uvm_object_utils_begin below.

   `uvm_object_utils_begin(riv_rdy_vld_source_seq)
   `uvm_object_utils_end

   `uvm_declare_p_sequencer(riv_rdy_vld_source_sequencer)

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //---------------------------------------------------------------------------------------------------------------------------------------
   // HINT: Add constraints here.
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name = "");
      super.new(name);
   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: body
   //
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task body ();
      const string msg_id = { get_type_name(), ".body" };

      // Ensure that a valid transaction item has been created.
      req = riv_rdy_vld_source_txn::type_id::create("req", .contxt(get_full_name()));

      // Request permission to send the item, randomize it and then send it.
      start_item(req, .sequencer(m_sequencer));
      if (! do_not_randomize) randomize_req();
      `uvm_info(msg_id, $sformatf("Generated %0s transaction.", req.get_type_name()), UVM_HIGH)
      `uvm_info(msg_id, $sformatf("Transaction details:\n%0s", req.sprint()), UVM_FULL)
      finish_item(req);
      `uvm_info(msg_id, $sformatf("Sent %0s transaction.", req.get_type_name()), UVM_HIGH)
      `uvm_info(msg_id, $sformatf("Final transaction details:\n%0s", req.sprint()), UVM_FULL)

   endtask: body
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: randomize_req
   //
   // Randomize transaction item 'req'.
   // HINT: Override this function in extended classes to implement different randomization.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void randomize_req ();
      const string msg_id = { get_type_name(), ".randomize_req" };

      if (! req.randomize) `uvm_fatal(msg_id, "Failed to randomize 'req'")

   endfunction: randomize_req
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_source_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SOURCE_SEQ_SVH_
