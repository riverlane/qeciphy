// SPDX-License-Identifier: BSD-2-Clause
// -----------------------------------------------------------------------------
// File        : qeciphy_etile.sv
// Description : Lint stub for Altera Agilex E-Tile transceiver module.
//               Declares the module interface for tooling convenience only.
//               No functional implementation is provided.
//
// Copyright (c) 2025 Riverlane Ltd.
// This file is not affiliated with or endorsed by Altera Corporation.
// The module names and ports are reproduced solely for build compatibility.
// -----------------------------------------------------------------------------

module qeciphy_etile (
    input  logic        reset,
    input  logic        pll_refclk0,
    input  logic        tx_coreclkin,
    input  logic        rx_coreclkin,
    output logic        tx_ready,
    output logic        rx_ready,
    output logic        tx_pma_ready,
    output logic        rx_pma_ready,
    output logic        tx_clkout,
    output logic        tx_clkout2,
    output logic        rx_clkout,
    output logic        rx_clkout2,
    output logic        tx_serial_data,
    output logic        tx_serial_data_n,
    input  logic        rx_serial_data,
    input  logic        rx_serial_data_n,
    output logic        rx_is_lockedtodata,
    input  logic [79:0] tx_parallel_data,
    output logic [79:0] rx_parallel_data
);

   assign tx_ready           = '0;
   assign rx_ready           = '0;
   assign tx_pma_ready       = '0;
   assign rx_pma_ready       = '0;
   assign tx_clkout          = '0;
   assign tx_clkout2         = '0;
   assign rx_clkout          = '0;
   assign rx_clkout2         = '0;
   assign tx_serial_data     = '0;
   assign tx_serial_data_n   = '0;
   assign rx_is_lockedtodata = '0;
   assign rx_parallel_data   = '0;

endmodule
