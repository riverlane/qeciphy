
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_AGENT_IF_SV_
`define RIV_PBUS_CONTROLLER_AGENT_IF_SV_

`include "riv_pbus_controller_agent_globals.svh"

//------------------------------------------------------------------------------------------------------------------------------------------
// Interface: riv_pbus_controller_agent_if
//
//------------------------------------------------------------------------------------------------------------------------------------------
interface riv_pbus_controller_agent_if (
   input logic rst_n
);

   // HINT: Always declare time parameters as used by this module. MUST be done as first statements after interface declaration.
   timeunit      `RIV_PBUS_CONTROLLER_AGENT_TIMEUNIT;
   timeprecision `RIV_PBUS_CONTROLLER_AGENT_TIMEPRECISION;

   logic pstate;
   logic preq;
   logic paccept;
   logic pactive;

endinterface : riv_pbus_controller_agent_if
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_AGENT_IF_SV_
