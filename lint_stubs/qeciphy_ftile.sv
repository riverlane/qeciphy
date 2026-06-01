// SPDX-License-Identifier: BSD-2-Clause
// -----------------------------------------------------------------------------
// File        : qeciphy_ftile.sv
// Description : Lint stub for Intel Agilex F-Tile transceiver module.
//               Declares the module interface for tooling convenience only.
//               No functional implementation is provided.
//
// Copyright (c) 2025 Riverlane Ltd.
// This file is not affiliated with or endorsed by Intel Corporation.
// The module names and ports are reproduced solely for build compatibility.
// -----------------------------------------------------------------------------

module qeciphy_ftile (
    input  logic        rx_cdr_refclk_link,
    input  logic        tx_pll_refclk_link,
    input  logic        tx_reset,
    input  logic        rx_reset,
    output logic        tx_reset_ack,
    output logic        rx_reset_ack,
    output logic        tx_ready,
    output logic        rx_ready,
    input  logic        tx_coreclkin,
    input  logic        rx_coreclkin,
    output logic        tx_clkout,
    output logic        tx_clkout2,
    output logic        rx_clkout,
    output logic        rx_clkout2,
    output logic        tx_serial_data,
    output logic        tx_serial_data_n,
    input  logic        rx_serial_data,
    input  logic        rx_serial_data_n,
    output logic        tx_pll_locked,
    output logic        rx_is_lockedtodata,
    output logic        rx_is_lockedtoref,
    output logic        tx_fifo_full,
    output logic        tx_fifo_empty,
    output logic        tx_pmaif_fifo_empty,
    output logic        tx_pmaif_fifo_pempty,
    output logic        tx_pmaif_fifo_pfull,
    input  logic [79:0] tx_parallel_data,
    output logic [79:0] rx_parallel_data
);

   assign tx_reset_ack         = '0;
   assign rx_reset_ack         = '0;
   assign tx_ready             = '0;
   assign rx_ready             = '0;
   assign tx_clkout            = '0;
   assign tx_clkout2           = '0;
   assign rx_clkout            = '0;
   assign rx_clkout2           = '0;
   assign tx_serial_data       = '0;
   assign tx_serial_data_n     = '0;
   assign tx_pll_locked        = '0;
   assign rx_is_lockedtodata   = '0;
   assign rx_is_lockedtoref    = '0;
   assign tx_fifo_full         = '0;
   assign tx_fifo_empty        = '0;
   assign tx_pmaif_fifo_empty  = '0;
   assign tx_pmaif_fifo_pempty = '0;
   assign tx_pmaif_fifo_pfull  = '0;
   assign rx_parallel_data     = '0;

endmodule
