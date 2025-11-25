// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef QECIPHY_ENV_PKG_SV_
`define QECIPHY_ENV_PKG_SV_

`include "qeciphy_env_globals.svh"
`include "qeciphy_env_miscio_if.sv"

//------------------------------------------------------------------------------------------------------------------------------------------
// Package: qeciphy_env_pkg
//
// Abstract:
//------------------------------------------------------------------------------------------------------------------------------------------
package qeciphy_env_pkg;

   timeunit      `QECIPHY_ENV_TIMEUNIT;
   timeprecision `QECIPHY_ENV_TIMEPRECISION;

   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // HINT: Import any packages needed by the environment here.
   import riv_pbus_controller_agent_pkg::*;
   import riv_rdy_vld_sink_agent_pkg::*;
   import riv_rdy_vld_source_agent_pkg::*;

   // These are the main parts of the environment.
   `include "qeciphy_env_common.svh"                 // Typedefs, macros, utilities etc. for use in package scope.
   `include "qeciphy_env_config.svh"                 // Configuration object class.
   `include "qeciphy_env_sequencer.svh"              // Agent's sequencer.

   `include "qeciphy_env_data_xfer_scoreboard.svh"
   `include "qeciphy_env_state_scoreboard.svh"

   // HINT: `include "qeciphy_env___covid___coverage.svh"

   `include "qeciphy_env.svh"                        // Environment top level.

   // Include the list of all the sequences included with this environment.
   `include "qeciphy_base_seq.svh"                   // The base sequence from which all environment sequences should extend.
   `include "qeciphy_env_sequences.svh"

endpackage : qeciphy_env_pkg
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_ENV_PKG_SV_
