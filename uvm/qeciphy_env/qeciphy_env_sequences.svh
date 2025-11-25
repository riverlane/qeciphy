
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_ENV_SEQUENCES_SVH_
`define QECIPHY_ENV_SEQUENCES_SVH_



   // List of sequences to be included from package
   `include "qeciphy_initialize_tb_seq.svh"
   `include "qeciphy_power_down_seq.svh"
   `include "qeciphy_power_up_seq.svh"
   `include "qeciphy_reset_seq.svh"
   `include "qeciphy_wait_link_ready_seq.svh"

   `include "qeciphy_null_test_seq.svh"         // Null test - just checks that the simulator fires up OK.
   `include "qeciphy_txrx_test_seq.svh"         // TxRx test - General random traffic to/from DUT.
   `include "qeciphy_power_state_test_seq.svh"  // Power-State test - Random power-down/-up cycles.
   `include "qeciphy_errors_test_seq.svh"
   `include "qeciphy_reset_test_seq.svh"
   `include "qeciphy_sleep_to_reset_test_seq.svh"
   // AUTO: End of list ** DO NOT REMOVE THIS LINE **

`endif  // QECIPHY_ENV_SEQUENCES_SVH_
