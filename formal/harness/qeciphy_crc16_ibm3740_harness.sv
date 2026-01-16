// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_crc16_ibm3740_harness;

   logic        clk_i;
   logic        rst_n_i;
   logic [63:0] tdata_i;
   logic        tvalid_i;
   logic [15:0] crc_o;
   logic        crc_valid_o;

   qeciphy_crc16_ibm3740 dut (
       .clk_i(clk_i),
       .rst_n_i(rst_n_i),
       .tdata_i(tdata_i),
       .tvalid_i(tvalid_i),
       .crc_o(crc_o),
       .crc_valid_o(crc_valid_o)
   );

   // No input assumptions necessary

endmodule
