// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_tx_boundary_gen_harness;

   logic clk_i;
   logic rst_n_i;
   logic faw_boundary_o;
   logic almost_faw_boundary_o;
   logic crc_boundary_o;

   qeciphy_tx_boundary_gen dut (.*);

   // No input assumptions necessary

endmodule

