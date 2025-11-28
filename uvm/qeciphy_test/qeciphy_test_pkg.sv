// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_TEST_PKG_SV_
`define QECIPHY_TEST_PKG_SV_

`include "qeciphy_test_globals.svh"   // Typedefs, macros, utilities etc. for use in simulation global scope.

//------------------------------------------------------------------------------------------------------------------------------------------
// Package: qeciphy_test_pkg
//
// Abstract:
//------------------------------------------------------------------------------------------------------------------------------------------
package qeciphy_test_pkg;

   timeunit      `QECIPHY_TEST_TIMEUNIT;
   timeprecision `QECIPHY_TEST_TIMEPRECISION;

   import uvm_pkg::*;
   `include "uvm_macros.svh"

   import qeciphy_env_pkg::*;    // Import the environment to be used by the tests.

   `include "qeciphy_test_common.svh"    // Typedefs, macros, utilities etc. for use in package scope.
   `include "qeciphy_base_test.svh"      // Base test class.

   // Include the list of all the tests that come as part of the TB.
   `include "qeciphy_tests.svh"

endpackage : qeciphy_test_pkg
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_TEST_PKG_SV_
