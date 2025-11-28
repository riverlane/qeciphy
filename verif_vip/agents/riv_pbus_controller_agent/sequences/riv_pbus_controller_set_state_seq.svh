
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_SET_STATE_SEQ_SVH_
`define RIV_PBUS_CONTROLLER_SET_STATE_SEQ_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_pbus_controller_set_state_seq
//
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_pbus_controller_set_state_seq extends riv_pbus_controller_seq;

   // Control/status variables - not randomized.
   // HINT: Declare control fields here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   // Randomized variables.
   rand logic new_state;         // State requested by this change.
   rand real  tsu_state2req_ns;  // Setup time (in ns) of PSTATE being valid to PREQ rising.
   rand real  th_req2state_ns;   // Hold time (in ns) of PSTATE from PREQ falling.
   rand real  tpd_accept2req_ns; // Propagation delay (in ns) from PACCEPT rising to PREQ falling.

   `uvm_object_utils_begin(riv_pbus_controller_set_state_seq)
   `uvm_object_utils_end

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //---------------------------------------------------------------------------------------------------------------------------------------
   constraint c_dflt_tsu_state2req  { soft tsu_state2req_ns  == 0.0; }     // May be overridden by inline constraints.
   constraint c_dflt_th_req2state   { soft th_req2state_ns   == 0.0; }     // May be overridden by inline constraints.
   constraint c_dflt_tpd_accept2req { soft tpd_accept2req_ns == 0.0; }     // May be overridden by inline constraints.
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
   // Task: randomize_req
   //
   // Randomize transaction item "req".
   // HINT: Randomize/set transaction item fields here (only needed if not overriding body() method).
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void randomize_req ();
      const string  msg_id = { get_type_name(), ".randomize_req" };
      int           rand_ok;

      rand_ok = req.randomize with {
         new_state         == local::new_state;
         tsu_state2req_ns  == local::tsu_state2req_ns;
         th_req2state_ns   == local::th_req2state_ns;
         tpd_accept2req_ns == local::tpd_accept2req_ns;
      };
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize req")

   endfunction: randomize_req
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_pbus_controller_set_state_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_SET_STATE_SEQ_SVH_
