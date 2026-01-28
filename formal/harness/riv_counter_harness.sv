// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Alex Crownshaw

module riv_counter_harness;

   logic        clk;
   logic        rst_n;
   logic [15:0] value;
   logic        load;
   logic        enable;
   logic        done;

   riv_counter dut (.*);

   // No input assumptions required

endmodule
