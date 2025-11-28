
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SINK_MONITOR_BFM_SV_
`define RIV_RDY_VLD_SINK_MONITOR_BFM_SV_

`include "riv_rdy_vld_sink_agent_globals.svh"

//------------------------------------------------------------------------------------------------------------------------------------------
// Module: riv_rdy_vld_sink_monitor_bfm
//
// Instance a BFM allowing the riv_rdy_vld_sink monitor-only agent interface to be connected into a TB via port connections.
// Normally instanced in top-level TBs to connect lower-level environments to DUT-internal signals - so all pins should be inputs.
// Also auto-adds the interface to the root of the ConfigDB using the supplied VIF_NAME parameter (defaults to riv_rdy_vld_sink_vif).
//------------------------------------------------------------------------------------------------------------------------------------------
module riv_rdy_vld_sink_monitor_bfm #(int WIDTH, string VIF_NAME = "riv_rdy_vld_sink_vif") (
   input logic                 clk,
   input logic                 rst_n,
   input logic                 valid,
   input logic                 ready,
   input logic [WIDTH - 1 : 0] data
);

   // HINT: Always declare time parameters as used by this module. MUST be done as first statements after module declaration.
   timeunit      `RIV_RDY_VLD_SINK_AGENT_TIMEUNIT;
   timeprecision `RIV_RDY_VLD_SINK_AGENT_TIMEPRECISION;

   import uvm_pkg::*;
   `include "uvm_macros.svh"

   riv_rdy_vld_sink_agent_if i_agent_if(.clk(clk), .rst_n(rst_n));

   initial begin
      if (WIDTH > i_agent_if.MAX_WIDTH) begin
         `uvm_fatal($sformatf("%m"), $sformatf("WIDTH (%0d) > MAX_WIDTH (%0d)", WIDTH, i_agent_if.MAX_WIDTH))
      end
   end

   assign i_agent_if.data_mask = {i_agent_if.MAX_WIDTH{1'b1}} >> (i_agent_if.MAX_WIDTH - WIDTH);
   assign i_agent_if.valid     = valid;
   assign i_agent_if.ready     = ready;
   assign i_agent_if.data      = data;

   // Add handle to the BFM's interface to the UVM ConfigDB.
   initial add_to_configdb(VIF_NAME);

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: add_to_configdb
   //
   // Add a handle to the BFM's interface into the UVM ConfigDB with the specified name.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task add_to_configdb(string name);
      uvm_config_db#(virtual riv_rdy_vld_sink_agent_if)::set(uvm_root::get(), "", name, i_agent_if);
   endtask : add_to_configdb
   //---------------------------------------------------------------------------------------------------------------------------------------

endmodule : riv_rdy_vld_sink_monitor_bfm
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SINK_MONITOR_BFM_SV_
