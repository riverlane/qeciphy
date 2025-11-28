
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SINK_AGENT_IF_SV_
`define RIV_RDY_VLD_SINK_AGENT_IF_SV_

`include "riv_rdy_vld_sink_agent_globals.svh"

//------------------------------------------------------------------------------------------------------------------------------------------
// Interface: riv_rdy_vld_sink_agent_if
//
//------------------------------------------------------------------------------------------------------------------------------------------
interface riv_rdy_vld_sink_agent_if (
   input logic clk,
   input logic rst_n
);

   timeunit      `RIV_RDY_VLD_SINK_AGENT_TIMEUNIT;
   timeprecision `RIV_RDY_VLD_SINK_AGENT_TIMEPRECISION;

   localparam int MAX_WIDTH = `RIV_RDY_VLD_SINK_AGENT_MAX_WIDTH;

   logic [MAX_WIDTH - 1 : 0] data_mask = {MAX_WIDTH{1'b1}};

   logic                     valid;
   logic                     ready;
   logic [MAX_WIDTH - 1 : 0] data;

endinterface : riv_rdy_vld_sink_agent_if
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SINK_AGENT_IF_SV_
