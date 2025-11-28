
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_AGENT_PKG_SV_
`define RIV_PBUS_CONTROLLER_AGENT_PKG_SV_

`include "riv_pbus_controller_agent_globals.svh"

//------------------------------------------------------------------------------------------------------------------------------------------
// Package: riv_pbus_controller_agent_pkg
//
//------------------------------------------------------------------------------------------------------------------------------------------
package riv_pbus_controller_agent_pkg;

   timeunit      `RIV_PBUS_CONTROLLER_AGENT_TIMEUNIT;
   timeprecision `RIV_PBUS_CONTROLLER_AGENT_TIMEPRECISION;

   import uvm_pkg::*;
   `include "uvm_macros.svh"

   `include "riv_pbus_controller_common.svh"         // Typedefs, constants, functions, tasks etc. exported from and used within this package.
   `include "riv_pbus_controller_config.svh"         // Configuration object for this agent, used by child components and sequences.
   `include "riv_pbus_controller_txn.svh"            // Base transaction class.
   `include "riv_pbus_controller_sequencer.svh"      // Sequencer.
   `include "riv_pbus_controller_driver.svh"         // Driver.
   `include "riv_pbus_controller_monitor.svh"        // Monitor.
   `include "riv_pbus_controller_seq.svh"            // Base sequence class.
   `include "riv_pbus_controller_coverage.svh"       // Agent coverage collector (optional - delete this line and file if not used).
   `include "riv_pbus_controller_scoreboard.svh"     // Agent scoreboard (optional - delete this line and file if not used).
   `include "riv_pbus_controller_agent.svh"          // Top-level of agent.

   `include "riv_pbus_controller_reg_adapter.svh"    // UVM RAL reg. adapter (optional - delete this line and file if agent doesn't support RAL).

   // Sequences that come as part of the agent package.
   `include "riv_pbus_controller_set_state_seq.svh"  // Executes a stage change


endpackage : riv_pbus_controller_agent_pkg
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_AGENT_PKG_SV_
