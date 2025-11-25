// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef _QECIPHY_ENV_IF_SV_
`define _QECIPHY_ENV_IF_SV_

`include "qeciphy_env_globals.svh"

//------------------------------------------------------------------------------------------------------------------------------------------
// Interface: qeciphy_env_miscio_if
//
// Abstract:
// Interface containing all miscellaneous I/O signals that are neither driven nor monitored by an agent.
// This can include internal signals that are used for monitoring/checking internal processes.
// Sequences, scoreboards, coverage-collectors etc. can drive and monitor these signals.
//------------------------------------------------------------------------------------------------------------------------------------------
interface qeciphy_env_miscio_if (
   input logic dut_aclk,
   input logic dut_rclk,
   input logic dut_fclk,
   input logic dut_arst_n,
   input logic tbphy_aclk,
   input logic tbphy_rclk,
   input logic tbphy_fclk,
   input logic tbphy_arst_n
);

   // HINT: Always declare time parameters as used by this module. MUST be done as first statements after interface declaration.
   timeunit      `QECIPHY_ENV_TIMEUNIT;
   timeprecision `QECIPHY_ENV_TIMEPRECISION;

   // Some signals that may be updated by test sequences to create easily visible test progress in waveforms.
   int    step_num;      // May be updated by sequences to show test progress in waveforms.
   string step_name;     // May be updated by sequences to show test progress in waveforms.
   int    num_errors;    // May be used to record when errors occur.

   logic [ 3:0] dut_status;
   logic [ 3:0] dut_ecode;
   logic [ 3:0] tbphy_status;
   logic [ 3:0] tbphy_ecode;

endinterface : qeciphy_env_miscio_if
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // _QECIPHY_ENV_IF_SV_
