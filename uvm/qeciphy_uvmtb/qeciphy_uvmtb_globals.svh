// All names defined here should be unique across the compilation unit so define them wisely - e.g. use QECIPHY_TB prefix.
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


//------------------------------------------------------------------------------------------------------------------------------------------

`ifndef QECIPHY_UVMTB_GLOBALS_SVH_
`define QECIPHY_UVMTB_GLOBALS_SVH_

// Unless already defined, define the time-unit and time-precision used by qeciphy_uvmtb objects and interface to be 1ns/1ps.
`ifndef QECIPHY_UVMTB_TIMEUNIT
`define QECIPHY_UVMTB_TIMEUNIT 1ns
`endif  // QECIPHY_UVMTB_TIMEUNIT

`ifndef QECIPHY_UVMTB_TIMEPRECISION
`define QECIPHY_UVMTB_TIMEPRECISION 1ps
`endif  // QECIPHY_UVMTB_TIMEPRECISION

`ifndef GT_TYPE // GT transceiver type
`define GT_TYPE "GTY" // default value
`endif

`endif  // QECIPHY_UVMTB_GLOBALS_SVH_
