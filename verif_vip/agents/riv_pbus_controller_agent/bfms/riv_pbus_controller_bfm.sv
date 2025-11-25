
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_BFM_SV_
`define RIV_PBUS_CONTROLLER_BFM_SV_

`include "riv_pbus_controller_agent_globals.svh"

//------------------------------------------------------------------------------------------------------------------------------------------
// Module: riv_pbus_controller_bfm
//
// Instance a BFM that allows the riv_pbus_controller agent interface to be connected into a TB via port connections.
// Also auto-adds the interface to the root of the ConfigDB using the supplied VIF_NAME parameter (defaults to riv_pbus_controller_vif).
//------------------------------------------------------------------------------------------------------------------------------------------
module riv_pbus_controller_bfm #(string VIF_NAME = "riv_pbus_controller_vif") (
   input  logic rst_n,
   output logic pstate,
   output logic preq,
   input  logic paccept,
   input  logic pactive
);

   timeunit      `RIV_PBUS_CONTROLLER_AGENT_TIMEUNIT;
   timeprecision `RIV_PBUS_CONTROLLER_AGENT_TIMEPRECISION;

   import uvm_pkg::*;
   `include "uvm_macros.svh"

   riv_pbus_controller_agent_if i_agent_if(.rst_n(rst_n));

   assign i_agent_if.paccept = paccept;
   assign i_agent_if.pactive = pactive;
   assign pstate             = i_agent_if.pstate;
   assign preq               = i_agent_if.preq;

   // Add handle to the BFM's interface to the UVM ConfigDB.
   initial add_to_configdb(VIF_NAME);

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: add_to_configdb
   //
   // Add a handle to the BFM's interface into the UVM ConfigDB with the specified name.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task add_to_configdb(string name);
      uvm_config_db#(virtual riv_pbus_controller_agent_if)::set(uvm_root::get(), "", name, i_agent_if);
   endtask : add_to_configdb
   //---------------------------------------------------------------------------------------------------------------------------------------

endmodule : riv_pbus_controller_bfm
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_BFM_SV_
