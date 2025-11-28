
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SINK_AGENT_PKG_SV_
`define RIV_RDY_VLD_SINK_AGENT_PKG_SV_



//------------------------------------------------------------------------------------------------------------------------------------------
// Package: riv_rdy_vld_sink_agent_pkg
//
//------------------------------------------------------------------------------------------------------------------------------------------
package riv_rdy_vld_sink_agent_pkg;


   import uvm_pkg::*;
   `include "uvm_macros.svh"
   `include "riv_rdy_vld_sink_agent_globals.svh"
   `include "riv_rdy_vld_sink_common.svh"         // Typedefs, constants, functions, tasks etc. exported from and used within this package.
   `include "riv_rdy_vld_sink_config.svh"         // Configuration object for this agent, used by child components and sequences.
   `include "riv_rdy_vld_sink_txn.svh"            // Base transaction class.
   `include "riv_rdy_vld_sink_sequencer.svh"      // Sequencer.
   `include "riv_rdy_vld_sink_driver.svh"         // Driver.
   `include "riv_rdy_vld_sink_monitor.svh"        // Monitor.
   `include "riv_rdy_vld_sink_seq.svh"            // Base sequence class.
   `include "riv_rdy_vld_sink_coverage.svh"       // Agent coverage collector (optional - delete this line and file if not used).
   `include "riv_rdy_vld_sink_scoreboard.svh"     // Agent scoreboard (optional - delete this line and file if not used).
   `include "riv_rdy_vld_sink_agent.svh"          // Top-level of agent.

   `include "riv_rdy_vld_sink_reg_adapter.svh"    // UVM RAL reg. adapter (optional - delete this line and file if agent doesn't support RAL).

   // Sequences that come as part of the agent package.
   `include "riv_rdy_vld_sink_1_word_seq.svh"
   `include "riv_rdy_vld_sink_infinite_seq.svh"
   `include "riv_rdy_vld_sink_multi_word_seq.svh"


endpackage : riv_rdy_vld_sink_agent_pkg
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SINK_AGENT_PKG_SV_
