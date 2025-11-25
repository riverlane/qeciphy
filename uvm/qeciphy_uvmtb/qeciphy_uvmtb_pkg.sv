// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef QECIPHY_UVMTB_PKG_SV_
`define QECIPHY_UVMTB_PKG_SV_

`include "qeciphy_uvmtb_globals.svh"   // Typedefs, macros, utilities etc. for use in simulation global scope.

//------------------------------------------------------------------------------------------------------------------------------------------
// Package: qeciphy_uvmtb_pkg
//
// Abstract:
// This package has all files used in qeciphy_uvmtb
//------------------------------------------------------------------------------------------------------------------------------------------
package qeciphy_uvmtb_pkg;

   timeunit      `QECIPHY_UVMTB_TIMEUNIT;
   timeprecision `QECIPHY_UVMTB_TIMEPRECISION;

   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // Import the environment to be used by this TB
   import qeciphy_env_pkg::*;
   import qeciphy_test_pkg::*;

   `include "qeciphy_uvmtb_common.svh"     // Typedefs, macros, utilities etc. for use in package scope.

endpackage : qeciphy_uvmtb_pkg
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_UVMTB_PKG_SV_
