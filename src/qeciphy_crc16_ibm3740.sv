// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// CRC-16/IBM-3740 Calculator
//------------------------------------------------------------------------------
// This module implements a CRC-16/IBM-3740 calculator for data integrity checking.
//
// Algorithm:
// - Polynomial: x^16 + x^12 + x^5 + 1 (0x1021 in hex)
// - Width: 16 bits
// - Initial value: 0xFFFF
// - Processes 64-bit data words in parallel
//
// Behavior:
// - Multi-stage pipeline for high-speed 64-bit parallel processing
// - Uses partial sum technique to manage combinational complexity
// - Data-dependent terms computed on tvalid_i, CRC updated on crc_update_en
// - Two-cycle latency from input valid to output valid
// - CRC accumulates across multiple input words until reset
//------------------------------------------------------------------------------

module qeciphy_crc16_ibm3740 (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic [63:0] tdata_i,
    input  logic        tvalid_i,
    output logic [15:0] crc_o,
    output logic        crc_valid_o
);

   logic   [15:0] crc_reg;  // Current CRC state
   logic   [15:0] crc_nxt;  // Next CRC state

   logic   [63:0] d;  // Input data

   logic   [ 3:0] dxor                                                          [15:0];  // Combinational partial data terms for each CRC bit
   logic   [ 3:0] dxor_reg                                                      [15:0];  // Registered partial data terms

   logic          crc_update_en;  // Delayed tvalid_i for CRC update timing
   logic   [ 1:0] valid_pipe;  // Valid signal shift register (2-cycle pipeline)

   integer        i;

   assign d             = tdata_i;
   assign crc_o         = crc_reg;
   assign crc_valid_o   = valid_pipe[1];
   assign crc_update_en = valid_pipe[0];

   // CRC state register - updates one cycle after data terms are registered
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_reg <= 16'hFFFF;
      end else if (crc_update_en) begin
         crc_reg <= crc_nxt;
      end
   end

   // Two-stage valid pipeline
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         valid_pipe <= 2'b00;
      end else begin
         valid_pipe <= {valid_pipe[0], tvalid_i};
      end
   end

   // Register data-dependent XOR terms when input is valid
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         for (i = 0; i < 16; i++) begin
            dxor_reg[i] <= '0;
         end
      end else if (tvalid_i) begin
         for (i = 0; i < 16; i++) begin
            dxor_reg[i] <= dxor[i];
         end
      end
   end

   // Combinational partial XOR terms for each CRC bit
   // Split into 4-bit chunks to manage timing and complexity
   // Each dxor[i] contains XOR of input data bits affecting CRC bit i
   // bit 0
   assign dxor[0][0] = d[0] ^ d[4] ^ d[8] ^ d[11] ^ d[12] ^ d[19] ^ d[20] ^ d[22] ^ d[26] ^ d[27];
   assign dxor[0][1] = d[28] ^ d[32] ^ d[33] ^ d[35] ^ d[42] ^ d[48] ^ d[49] ^ d[51] ^ d[52] ^ d[55];
   assign dxor[0][2] = d[56] ^ d[58] ^ d[63];
   assign dxor[0][3] = 1'b0;

   // bit 1
   assign dxor[1][0] = d[1] ^ d[5] ^ d[9] ^ d[12] ^ d[13] ^ d[20] ^ d[21] ^ d[23] ^ d[27] ^ d[28];
   assign dxor[1][1] = d[29] ^ d[33] ^ d[34] ^ d[36] ^ d[43] ^ d[49] ^ d[50] ^ d[52] ^ d[53] ^ d[56];
   assign dxor[1][2] = d[57] ^ d[59];
   assign dxor[1][3] = 1'b0;

   // bit 2
   assign dxor[2][0] = d[2] ^ d[6] ^ d[10] ^ d[13] ^ d[14] ^ d[21] ^ d[22] ^ d[24] ^ d[28] ^ d[29];
   assign dxor[2][1] = d[30] ^ d[34] ^ d[35] ^ d[37] ^ d[44] ^ d[50] ^ d[51] ^ d[53] ^ d[54] ^ d[57];
   assign dxor[2][2] = d[58] ^ d[60];
   assign dxor[2][3] = 1'b0;

   // bit 3
   assign dxor[3][0] = d[3] ^ d[7] ^ d[11] ^ d[14] ^ d[15] ^ d[22] ^ d[23] ^ d[25] ^ d[29] ^ d[30];
   assign dxor[3][1] = d[31] ^ d[35] ^ d[36] ^ d[38] ^ d[45] ^ d[51] ^ d[52] ^ d[54] ^ d[55] ^ d[58];
   assign dxor[3][2] = d[59] ^ d[61];
   assign dxor[3][3] = 1'b0;

   // bit 4
   assign dxor[4][0] = d[4] ^ d[8] ^ d[12] ^ d[15] ^ d[16] ^ d[23] ^ d[24] ^ d[26] ^ d[30] ^ d[31];
   assign dxor[4][1] = d[32] ^ d[36] ^ d[37] ^ d[39] ^ d[46] ^ d[52] ^ d[53] ^ d[55] ^ d[56] ^ d[59];
   assign dxor[4][2] = d[60] ^ d[62];
   assign dxor[4][3] = 1'b0;

   // bit 5
   assign dxor[5][0] = d[0] ^ d[4] ^ d[5] ^ d[8] ^ d[9] ^ d[11] ^ d[12] ^ d[13] ^ d[16];
   assign dxor[5][1] = d[17] ^ d[19] ^ d[20] ^ d[22] ^ d[24] ^ d[25] ^ d[26] ^ d[28] ^ d[31];
   assign dxor[5][2] = d[35] ^ d[37] ^ d[38] ^ d[40] ^ d[42] ^ d[47] ^ d[48] ^ d[49] ^ d[51];
   assign dxor[5][3] = d[52] ^ d[53] ^ d[54] ^ d[55] ^ d[57] ^ d[58] ^ d[60] ^ d[61];

   // bit 6
   assign dxor[6][0] = d[1] ^ d[5] ^ d[6] ^ d[9] ^ d[10] ^ d[12] ^ d[13] ^ d[14] ^ d[17];
   assign dxor[6][1] = d[18] ^ d[20] ^ d[21] ^ d[23] ^ d[25] ^ d[26] ^ d[27] ^ d[29] ^ d[32];
   assign dxor[6][2] = d[36] ^ d[38] ^ d[39] ^ d[41] ^ d[43] ^ d[48] ^ d[49] ^ d[50] ^ d[52];
   assign dxor[6][3] = d[53] ^ d[54] ^ d[55] ^ d[56] ^ d[58] ^ d[59] ^ d[61] ^ d[62];

   // bit 7
   assign dxor[7][0] = d[2] ^ d[6] ^ d[7] ^ d[10] ^ d[11] ^ d[13] ^ d[14] ^ d[15] ^ d[18];
   assign dxor[7][1] = d[19] ^ d[21] ^ d[22] ^ d[24] ^ d[26] ^ d[27] ^ d[28] ^ d[30] ^ d[33];
   assign dxor[7][2] = d[37] ^ d[39] ^ d[40] ^ d[42] ^ d[44] ^ d[49] ^ d[50] ^ d[51] ^ d[53];
   assign dxor[7][3] = d[54] ^ d[55] ^ d[56] ^ d[57] ^ d[59] ^ d[60] ^ d[62] ^ d[63];

   // bit 8
   assign dxor[8][0] = d[3] ^ d[7] ^ d[8] ^ d[11] ^ d[12] ^ d[14] ^ d[15] ^ d[16] ^ d[19];
   assign dxor[8][1] = d[20] ^ d[22] ^ d[23] ^ d[25] ^ d[27] ^ d[28] ^ d[29] ^ d[31] ^ d[34];
   assign dxor[8][2] = d[38] ^ d[40] ^ d[41] ^ d[43] ^ d[45] ^ d[50] ^ d[51] ^ d[52];
   assign dxor[8][3] = d[54] ^ d[55] ^ d[56] ^ d[57] ^ d[58] ^ d[60] ^ d[61] ^ d[63];

   // bit 9
   assign dxor[9][0] = d[4] ^ d[8] ^ d[9] ^ d[12] ^ d[13] ^ d[15] ^ d[16] ^ d[17] ^ d[20];
   assign dxor[9][1] = d[21] ^ d[23] ^ d[24] ^ d[26] ^ d[28] ^ d[29] ^ d[30] ^ d[32] ^ d[35];
   assign dxor[9][2] = d[39] ^ d[41] ^ d[42] ^ d[44] ^ d[46] ^ d[51] ^ d[52] ^ d[53] ^ d[55];
   assign dxor[9][3] = d[56] ^ d[57] ^ d[58] ^ d[59] ^ d[61] ^ d[62];

   // bit 10
   assign dxor[10][0] = d[5] ^ d[9] ^ d[10] ^ d[13] ^ d[14] ^ d[16] ^ d[17] ^ d[18] ^ d[21];
   assign dxor[10][1] = d[22] ^ d[24] ^ d[25] ^ d[27] ^ d[29] ^ d[30] ^ d[31] ^ d[33] ^ d[36];
   assign dxor[10][2] = d[40] ^ d[42] ^ d[43] ^ d[45] ^ d[47] ^ d[52] ^ d[53] ^ d[54] ^ d[56];
   assign dxor[10][3] = d[57] ^ d[58] ^ d[59] ^ d[60] ^ d[62] ^ d[63];

   // bit 11
   assign dxor[11][0] = d[6] ^ d[10] ^ d[11] ^ d[14] ^ d[15] ^ d[17] ^ d[18] ^ d[19];
   assign dxor[11][1] = d[22] ^ d[23] ^ d[25] ^ d[26] ^ d[28] ^ d[30] ^ d[31] ^ d[32];
   assign dxor[11][2] = d[34] ^ d[37] ^ d[41] ^ d[43] ^ d[44] ^ d[46] ^ d[48] ^ d[53];
   assign dxor[11][3] = d[54] ^ d[55] ^ d[57] ^ d[58] ^ d[59] ^ d[60] ^ d[61] ^ d[63];

   // bit 12
   assign dxor[12][0] = d[0] ^ d[4] ^ d[7] ^ d[8] ^ d[15] ^ d[16] ^ d[18];
   assign dxor[12][1] = d[22] ^ d[23] ^ d[24] ^ d[28] ^ d[29] ^ d[31] ^ d[38];
   assign dxor[12][2] = d[44] ^ d[45] ^ d[47] ^ d[48] ^ d[51] ^ d[52];
   assign dxor[12][3] = d[54] ^ d[59] ^ d[60] ^ d[61] ^ d[62] ^ d[63];

   // bit 13
   assign dxor[13][0] = d[1] ^ d[5] ^ d[8] ^ d[9] ^ d[16] ^ d[17] ^ d[19];
   assign dxor[13][1] = d[23] ^ d[24] ^ d[25] ^ d[29] ^ d[30] ^ d[32];
   assign dxor[13][2] = d[39] ^ d[45] ^ d[46] ^ d[48] ^ d[49] ^ d[52];
   assign dxor[13][3] = d[53] ^ d[55] ^ d[60] ^ d[61] ^ d[62] ^ d[63];

   // bit 14
   assign dxor[14][0] = d[2] ^ d[6] ^ d[9] ^ d[10] ^ d[17] ^ d[18];
   assign dxor[14][1] = d[20] ^ d[24] ^ d[25] ^ d[26] ^ d[30] ^ d[31];
   assign dxor[14][2] = d[33] ^ d[40] ^ d[46] ^ d[47] ^ d[49] ^ d[50];
   assign dxor[14][3] = d[53] ^ d[54] ^ d[56] ^ d[61] ^ d[62] ^ d[63];

   // bit 15
   assign dxor[15][0] = d[3] ^ d[7] ^ d[10] ^ d[11] ^ d[18] ^ d[19];
   assign dxor[15][1] = d[21] ^ d[25] ^ d[26] ^ d[27] ^ d[31] ^ d[32];
   assign dxor[15][2] = d[34] ^ d[41] ^ d[47] ^ d[48] ^ d[50] ^ d[51];
   assign dxor[15][3] = d[54] ^ d[55] ^ d[57] ^ d[62] ^ d[63];

   // Final CRC calculation: combine current CRC state with registered data terms
   // Each bit computed as XOR of relevant current CRC bits and all data-dependent terms
   assign crc_nxt[0] = crc_reg[0] ^ crc_reg[1] ^ crc_reg[3] ^ crc_reg[4] ^ crc_reg[7] ^ crc_reg[8] ^ crc_reg[10] ^ crc_reg[15] ^ dxor_reg[0][0] ^ dxor_reg[0][1] ^ dxor_reg[0][2] ^ dxor_reg[0][3];

   assign crc_nxt[1] = crc_reg[1] ^ crc_reg[2] ^ crc_reg[4] ^ crc_reg[5] ^ crc_reg[8] ^ crc_reg[9] ^ crc_reg[11] ^ dxor_reg[1][0] ^ dxor_reg[1][1] ^ dxor_reg[1][2] ^ dxor_reg[1][3];

   assign crc_nxt[2] = crc_reg[2] ^ crc_reg[3] ^ crc_reg[5] ^ crc_reg[6] ^ crc_reg[9] ^ crc_reg[10] ^ crc_reg[12] ^ dxor_reg[2][0] ^ dxor_reg[2][1] ^ dxor_reg[2][2] ^ dxor_reg[2][3];

   assign crc_nxt[3] = crc_reg[3] ^ crc_reg[4] ^ crc_reg[6] ^ crc_reg[7] ^ crc_reg[10] ^ crc_reg[11] ^ crc_reg[13] ^ dxor_reg[3][0] ^ dxor_reg[3][1] ^ dxor_reg[3][2] ^ dxor_reg[3][3];

   assign crc_nxt[4] = crc_reg[4] ^ crc_reg[5] ^ crc_reg[7] ^ crc_reg[8] ^ crc_reg[11] ^ crc_reg[12] ^ crc_reg[14] ^ dxor_reg[4][0] ^ dxor_reg[4][1] ^ dxor_reg[4][2] ^ dxor_reg[4][3];

   assign crc_nxt[5] = crc_reg[0] ^ crc_reg[1] ^ crc_reg[3] ^ crc_reg[4] ^ crc_reg[5] ^ crc_reg[6] ^ crc_reg[7] ^ crc_reg[9] ^ crc_reg[10] ^ crc_reg[12] ^ crc_reg[13] ^ dxor_reg[5][0] ^ dxor_reg[5][1] ^ dxor_reg[5][2] ^ dxor_reg[5][3];

   assign crc_nxt[6] = crc_reg[0] ^ crc_reg[1] ^ crc_reg[2] ^ crc_reg[4] ^ crc_reg[5] ^ crc_reg[6] ^ crc_reg[7] ^ crc_reg[8] ^ crc_reg[10] ^ crc_reg[11] ^ crc_reg[13] ^ crc_reg[14] ^ dxor_reg[6][0] ^ dxor_reg[6][1] ^ dxor_reg[6][2] ^ dxor_reg[6][3];

   assign crc_nxt[7] = crc_reg[1] ^ crc_reg[2] ^ crc_reg[3] ^ crc_reg[5] ^ crc_reg[6] ^ crc_reg[7] ^ crc_reg[8] ^ crc_reg[9] ^ crc_reg[11] ^ crc_reg[12] ^ crc_reg[14] ^ crc_reg[15] ^ dxor_reg[7][0] ^ dxor_reg[7][1] ^ dxor_reg[7][2] ^ dxor_reg[7][3];

   assign crc_nxt[8] = crc_reg[2] ^ crc_reg[3] ^ crc_reg[4] ^ crc_reg[6] ^ crc_reg[7] ^ crc_reg[8] ^ crc_reg[9] ^ crc_reg[10] ^ crc_reg[12] ^ crc_reg[13] ^ crc_reg[15] ^ dxor_reg[8][0] ^ dxor_reg[8][1] ^ dxor_reg[8][2] ^ dxor_reg[8][3];

   assign crc_nxt[9] = crc_reg[3] ^ crc_reg[4] ^ crc_reg[5] ^ crc_reg[7] ^ crc_reg[8] ^ crc_reg[9] ^ crc_reg[10] ^ crc_reg[11] ^ crc_reg[13] ^ crc_reg[14] ^ dxor_reg[9][0] ^ dxor_reg[9][1] ^ dxor_reg[9][2] ^ dxor_reg[9][3];

   assign crc_nxt[10] = crc_reg[4] ^ crc_reg[5] ^ crc_reg[6] ^ crc_reg[8] ^ crc_reg[9] ^ crc_reg[10] ^ crc_reg[11] ^ crc_reg[12] ^ crc_reg[14] ^ crc_reg[15] ^ dxor_reg[10][0] ^ dxor_reg[10][1] ^ dxor_reg[10][2] ^ dxor_reg[10][3];

   assign crc_nxt[11] = crc_reg[0] ^ crc_reg[5] ^ crc_reg[6] ^ crc_reg[7] ^ crc_reg[9] ^ crc_reg[10] ^ crc_reg[11] ^ crc_reg[12] ^ crc_reg[13] ^ crc_reg[15] ^ dxor_reg[11][0] ^ dxor_reg[11][1] ^ dxor_reg[11][2] ^ dxor_reg[11][3];

   assign crc_nxt[12] = crc_reg[0] ^ crc_reg[3] ^ crc_reg[4] ^ crc_reg[6] ^ crc_reg[11] ^ crc_reg[12] ^ crc_reg[13] ^ crc_reg[14] ^ crc_reg[15] ^ dxor_reg[12][0] ^ dxor_reg[12][1] ^ dxor_reg[12][2] ^ dxor_reg[12][3];

   assign crc_nxt[13] = crc_reg[0] ^ crc_reg[1] ^ crc_reg[4] ^ crc_reg[5] ^ crc_reg[7] ^ crc_reg[12] ^ crc_reg[13] ^ crc_reg[14] ^ crc_reg[15] ^ dxor_reg[13][0] ^ dxor_reg[13][1] ^ dxor_reg[13][2] ^ dxor_reg[13][3];

   assign crc_nxt[14] = crc_reg[1] ^ crc_reg[2] ^ crc_reg[5] ^ crc_reg[6] ^ crc_reg[8] ^ crc_reg[13] ^ crc_reg[14] ^ crc_reg[15] ^ dxor_reg[14][0] ^ dxor_reg[14][1] ^ dxor_reg[14][2] ^ dxor_reg[14][3];

   assign crc_nxt[15] = crc_reg[0] ^ crc_reg[2] ^ crc_reg[3] ^ crc_reg[6] ^ crc_reg[7] ^ crc_reg[9] ^ crc_reg[14] ^ crc_reg[15] ^ dxor_reg[15][0] ^ dxor_reg[15][1] ^ dxor_reg[15][2] ^ dxor_reg[15][3];

endmodule
