
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_BASE_SEQ_SVH_
`define QECIPHY_BASE_SEQ_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_base_seq
//
// Abstract:
// This is the base sequence class from which all qeciphy sequences should be extended.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_base_seq extends uvm_sequence;

   `uvm_object_utils_begin(qeciphy_base_seq)
   `uvm_object_utils_end

   `uvm_declare_p_sequencer(qeciphy_env_sequencer)

   // Control/status variables - not randomized.
   // HINT: Declare control fields here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   // Randomized variables.
   // HINT: Declare randomizable variables here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   // Constraints
   // HINT: Add constraints here.


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function new(string name = "");
      super.new(name);
     // set_automatic_phase_objection(1);
   endfunction : new
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: body
   //
   // HINT: Add sequence actions to this task (this is the task that runs after a sequence is started on a sequencer).
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task body ();
      const string msg_id = { get_type_name(), ".body" };

      // HINT: Replace the following if you want the base-class sequence to actually do stuff.
      `uvm_fatal(msg_id, "This is a base-class sequence - DO NOT RUN")

   endtask: body
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_base_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_BASE_SEQ_SVH_
