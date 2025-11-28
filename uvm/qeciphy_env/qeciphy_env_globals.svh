//------------------------------------------------------------------------------------------------------------------------------------------
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA



`ifndef QECIPHY_ENV_GLOBALS_SVH_
`define QECIPHY_ENV_GLOBALS_SVH_

// Unless already defined, define the time-unit and time-precision used by qeciphy_env objects and interface to be 1ns/1ps.
`ifndef QECIPHY_ENV_TIMEUNIT
`define QECIPHY_ENV_TIMEUNIT 1ns
`endif  // QECIPHY_ENV_TIMEUNIT

`ifndef QECIPHY_ENV_TIMEPRECISION
`define QECIPHY_ENV_TIMEPRECISION 1ps
`endif  // QECIPHY_ENV_TIMEPRECISION

`endif  // QECIPHY_ENV_GLOBALS_SVH_
