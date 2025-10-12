// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Dogancan Davutoglu

module qeciphy_crc8_smbus (
    input  logic [7:0] data_i,
    input  logic       valid_i,
    output logic [7:0] crc_o
);

   // CRC algorithm              : CRC-8/SMBUS
   // CRC polynomial coefficients: x^8 + x^2 + x + 1
   //                              0x7 (hex)
   // CRC width:                   8 bits
   // CRC shift direction:         left (big endian)
   // Input word width:            8 bits

   // -------------------------------------------------------------
   // Local declaration
   // -------------------------------------------------------------

   localparam c = 8'd0;
   logic [7:0] d;
   logic [7:0] c_nxt;

   // -------------------------------------------------------------
   // Assignments
   // -------------------------------------------------------------

   assign d = data_i;
   assign crc_o = valid_i ? c_nxt : 8'd0;

   // -------------------------------------------------------------
   // Compute CRC in parallel
   // -------------------------------------------------------------

   assign c_nxt[0] = c[0] ^ c[6] ^ c[7] ^ d[0] ^ d[6] ^ d[7];
   assign c_nxt[1] = c[0] ^ c[1] ^ c[6] ^ d[0] ^ d[1] ^ d[6];
   assign c_nxt[2] = c[0] ^ c[1] ^ c[2] ^ c[6] ^ d[0] ^ d[1] ^ d[2] ^ d[6];
   assign c_nxt[3] = c[1] ^ c[2] ^ c[3] ^ c[7] ^ d[1] ^ d[2] ^ d[3] ^ d[7];
   assign c_nxt[4] = c[2] ^ c[3] ^ c[4] ^ d[2] ^ d[3] ^ d[4];
   assign c_nxt[5] = c[3] ^ c[4] ^ c[5] ^ d[3] ^ d[4] ^ d[5];
   assign c_nxt[6] = c[4] ^ c[5] ^ c[6] ^ d[4] ^ d[5] ^ d[6];
   assign c_nxt[7] = c[5] ^ c[6] ^ c[7] ^ d[5] ^ d[6] ^ d[7];

endmodule  // qeciphy_crc8_smbus
