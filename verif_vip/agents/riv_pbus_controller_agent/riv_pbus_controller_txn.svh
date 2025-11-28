
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_TXN_SVH_
`define RIV_PBUS_CONTROLLER_TXN_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_pbus_controller_txn
//
// This is the base class for all dummy transactions.
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_pbus_controller_txn extends uvm_sequence_item;

   // Control/status variables - not randomized.
   int    unsigned  m_item_num;   // Records the Number of transactions, including this one, transmitted by driver or received by monitor.
   string           m_src;        // Identifies transaction source (e.g. driver instance name).
   logic            state;
   logic            active;

   // Randomized variables.
   rand logic new_state;         // State requested by this change.
   rand real  tsu_state2req_ns;  // Setup time (in ns) of PSTATE being valid to PREQ rising.
   rand real  th_req2state_ns;   // Hold time (in ns) of PSTATE from PREQ falling.
   rand real  tpd_accept2req_ns; // Propagation delay (in ns) from PACCEPT rising to PREQ falling.

   `uvm_object_utils_begin(riv_pbus_controller_txn)
      `uvm_field_int   (m_item_num,        UVM_DEFAULT | UVM_UNSIGNED)
      `uvm_field_string(m_src,             UVM_DEFAULT               )
      `uvm_field_int   (state,             UVM_DEFAULT | UVM_BIN     )
      `uvm_field_int   (active,            UVM_DEFAULT | UVM_BIN     )
      `uvm_field_int   (new_state,         UVM_DEFAULT | UVM_BIN     )
      `uvm_field_real  (tsu_state2req_ns,  UVM_DEFAULT               )
      `uvm_field_real  (th_req2state_ns,   UVM_DEFAULT               )
      `uvm_field_real  (tpd_accept2req_ns, UVM_DEFAULT               )
   `uvm_object_utils_end

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
   function new(string name = "riv_pbus_controller_txn");
      super.new(name);
   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_pbus_controller_txn
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_TXN_SVH_
