// All names defined here should be unique across the compilation unit so define them wisely - e.g. use QECIPHY_TEST prefix.
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


//------------------------------------------------------------------------------------------------------------------------------------------

`ifndef QECIPHY_TEST_GLOBALS_SVH_
`define QECIPHY_TEST_GLOBALS_SVH_

// Unless already defined, define the time-unit and time-precision used by qeciphy_test objects to be 1ns/1ps.
`ifndef QECIPHY_TEST_TIMEUNIT
`define QECIPHY_TEST_TIMEUNIT 1ns
`endif  // QECIPHY_TEST_TIMEUNIT

`ifndef QECIPHY_TEST_TIMEPRECISION
`define QECIPHY_TEST_TIMEPRECISION 1ps
`endif  // QECIPHY_TEST_TIMEPRECISION

`endif  // QECIPHY_TEST_GLOBALS_SVH_
