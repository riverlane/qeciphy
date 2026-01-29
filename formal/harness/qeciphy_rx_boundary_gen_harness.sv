// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_rx_boundary_gen_harness;

   logic        clk_i;
   logic        rst_n_i;
   logic [63:0] tdata_i;
   logic [63:0] tdata_o;
   logic        enable_i;
   logic        locked_o;
   logic        faw_boundary_o;
   logic        crc_boundary_o;

   qeciphy_rx_boundary_gen dut (.*);

   // No input assumptions necessary

endmodule
