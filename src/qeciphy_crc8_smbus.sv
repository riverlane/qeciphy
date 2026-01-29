// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Dogancan Davutoglu

//------------------------------------------------------------------------------
// CRC-8/SMBUS Calculator
//------------------------------------------------------------------------------
// This module implements a CRC-8/SMBUS calculator for data integrity checking.
//
// Algorithm:
// - Polynomial: x^8 + x^2 + x + 1 (0x7 in hex)
// - Width: 8 bits
// - Shift direction: left (big endian)
// - Initial value: 0x00
//
// Behavior:
// - Processes 8-bit tdata_i when tvalid_i is asserted
// - Outputs updated CRC value and validity flag with one cycle latency
// - CRC accumulates across multiple input bytes until reset
//------------------------------------------------------------------------------

module qeciphy_crc8_smbus (
    input  logic       clk_i,
    input  logic       rst_n_i,
    input  logic [7:0] tdata_i,
    input  logic       tvalid_i,
    output logic [7:0] crc_o,
    output logic       crc_valid_o
);

   logic [7:0] d;
   logic [7:0] c;
   logic [7:0] c_nxt;

   assign d = tdata_i;
   assign crc_o = c;

   // Accumulate CRC value
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         c <= 8'd0;
      end else if (tvalid_i) begin
         c <= c_nxt;
      end
   end

   // Output valid flag follows input valid with one cycle delay
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_valid_o <= 1'b0;
      end else begin
         crc_valid_o <= tvalid_i;
      end
   end

   // Each bit of next CRC value computed as XOR of current CRC bits
   // and input data bits according to CRC-8/SMBUS polynomial
   assign c_nxt[0] = c[0] ^ c[6] ^ c[7] ^ d[0] ^ d[6] ^ d[7];
   assign c_nxt[1] = c[0] ^ c[1] ^ c[6] ^ d[0] ^ d[1] ^ d[6];
   assign c_nxt[2] = c[0] ^ c[1] ^ c[2] ^ c[6] ^ d[0] ^ d[1] ^ d[2] ^ d[6];
   assign c_nxt[3] = c[1] ^ c[2] ^ c[3] ^ c[7] ^ d[1] ^ d[2] ^ d[3] ^ d[7];
   assign c_nxt[4] = c[2] ^ c[3] ^ c[4] ^ d[2] ^ d[3] ^ d[4];
   assign c_nxt[5] = c[3] ^ c[4] ^ c[5] ^ d[3] ^ d[4] ^ d[5];
   assign c_nxt[6] = c[4] ^ c[5] ^ c[6] ^ d[4] ^ d[5] ^ d[6];
   assign c_nxt[7] = c[5] ^ c[6] ^ c[7] ^ d[5] ^ d[6] ^ d[7];

endmodule  // qeciphy_crc8_smbus
