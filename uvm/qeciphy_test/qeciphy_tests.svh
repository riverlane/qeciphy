
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_TESTS_SVH_
`define QECIPHY_TESTS_SVH_

   // List of sequences to be included from package
   `include "qeciphy_null_test.svh"          // Null test - just checks that the simulator fires up OK.

   `include "qeciphy_smoke_test.svh"         // Smoke test - Short, "I'm alive" test
   `include "qeciphy_txrx_test.svh"          // TxRx test - General random traffic to/from DUT.
   `include "qeciphy_errors_test.svh"
   // AUTO: End of list ** DO NOT REMOVE THIS LINE **

`endif // QECIPHY_TESTS_SVH_
