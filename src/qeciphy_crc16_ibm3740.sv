// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_crc16_ibm3740 (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [63:0] i_data,
    input  logic        i_valid,
    output logic [15:0] o_crc
);

   // -------------------------------------------------------------
   // Local declaration
   // -------------------------------------------------------------

   logic [15:0] c;
   logic [15:0] c_nxt;
   logic [63:0] d;

   // -------------------------------------------------------------
   // Assignments
   // -------------------------------------------------------------

   assign d = i_data;
   assign o_crc = c;

   // -------------------------------------------------------------
   // Compute CRC in parallel
   // -------------------------------------------------------------

   // Algorithm: 
   // 1. Denote N = data width; M = polynomial width
   // 2. Implement CRC generator routine for a given polynomial using serial shifting.
   // 3. Build matrix H1: Compute the M-bit CRC for an N-bit one-hot input keeping the initial CRC value to zero. 
   //    For a 4-bit input, this means only considering the input values: 0x1, 0x2, 0x4, and 0x8.
   // 4. Build matrix H2: Compute the M-bit CRC for an M-bit one-hot initial CRC and input zero. 
   //    For a 3-bit CRC, this means only considering the initial CRC values: 0x1, 0x2, and 0x4.
   // 5. Write the matrix H1 as [CRC_out x Data_in], where each column has M bits and each row has N bits. 
   //    Similarly, write H2 as [CRC_out x CRC_init], forming an M x M matrix. For each bit in CRC_out, identify the components 
   //    from both Data_in and CRC_init that are set to 1. These are the contributing components for that specific bit in CRC_out.

   // Implementation: CRC-16/IBM-3740 (width=16 poly=0x1021 init=0xffff refin=false refout=false xorout=0x0000 check=0x29b1 residue=0x0000)

   always_ff @(posedge clk) begin
      if (~rst_n) begin
         c <= 16'hFFFF;
      end else if (i_valid) begin
         c <= c_nxt;
      end
   end

   assign c_nxt[0] = d[0]^d[4]^d[8]^d[11]^d[12]^d[19]^d[20]^d[22]^d[26]^d[27]^d[28]^d[32]^d[33]^d[35]^d[42]^d[48]^d[49]^d[51]^d[52]^d[55]^d[56]^d[58]^d[63]^c[0]^c[1]^c[3]^c[4]^c[7]^c[8]^c[10]^c[15];
   assign c_nxt[1] = d[1]^d[5]^d[9]^d[12]^d[13]^d[20]^d[21]^d[23]^d[27]^d[28]^d[29]^d[33]^d[34]^d[36]^d[43]^d[49]^d[50]^d[52]^d[53]^d[56]^d[57]^d[59]^c[1]^c[2]^c[4]^c[5]^c[8]^c[9]^c[11];
   assign c_nxt[2] = d[2]^d[6]^d[10]^d[13]^d[14]^d[21]^d[22]^d[24]^d[28]^d[29]^d[30]^d[34]^d[35]^d[37]^d[44]^d[50]^d[51]^d[53]^d[54]^d[57]^d[58]^d[60]^c[2]^c[3]^c[5]^c[6]^c[9]^c[10]^c[12];
   assign c_nxt[3] = d[3]^d[7]^d[11]^d[14]^d[15]^d[22]^d[23]^d[25]^d[29]^d[30]^d[31]^d[35]^d[36]^d[38]^d[45]^d[51]^d[52]^d[54]^d[55]^d[58]^d[59]^d[61]^c[3]^c[4]^c[6]^c[7]^c[10]^c[11]^c[13];
   assign c_nxt[4] = d[4]^d[8]^d[12]^d[15]^d[16]^d[23]^d[24]^d[26]^d[30]^d[31]^d[32]^d[36]^d[37]^d[39]^d[46]^d[52]^d[53]^d[55]^d[56]^d[59]^d[60]^d[62]^c[4]^c[5]^c[7]^c[8]^c[11]^c[12]^c[14];
   assign c_nxt[5] = d[0]^d[4]^d[5]^d[8]^d[9]^d[11]^d[12]^d[13]^d[16]^d[17]^d[19]^d[20]^d[22]^d[24]^d[25]^d[26]^d[28]^d[31]^d[35]^d[37]^d[38]^d[40]^d[42]^d[47]^d[48]^d[49]^d[51]^d[52]^d[53]^d[54]^d[55]^d[57]^d[58]^d[60]^d[61]^c[0]^c[1]^c[3]^c[4]^c[5]^c[6]^c[7]^c[9]^c[10]^c[12]^c[13];
   assign c_nxt[6] = d[1]^d[5]^d[6]^d[9]^d[10]^d[12]^d[13]^d[14]^d[17]^d[18]^d[20]^d[21]^d[23]^d[25]^d[26]^d[27]^d[29]^d[32]^d[36]^d[38]^d[39]^d[41]^d[43]^d[48]^d[49]^d[50]^d[52]^d[53]^d[54]^d[55]^d[56]^d[58]^d[59]^d[61]^d[62]^c[0]^c[1]^c[2]^c[4]^c[5]^c[6]^c[7]^c[8]^c[10]^c[11]^c[13]^c[14];
   assign c_nxt[7] = d[2]^d[6]^d[7]^d[10]^d[11]^d[13]^d[14]^d[15]^d[18]^d[19]^d[21]^d[22]^d[24]^d[26]^d[27]^d[28]^d[30]^d[33]^d[37]^d[39]^d[40]^d[42]^d[44]^d[49]^d[50]^d[51]^d[53]^d[54]^d[55]^d[56]^d[57]^d[59]^d[60]^d[62]^d[63]^c[1]^c[2]^c[3]^c[5]^c[6]^c[7]^c[8]^c[9]^c[11]^c[12]^c[14]^c[15];
   assign c_nxt[8] = d[3]^d[7]^d[8]^d[11]^d[12]^d[14]^d[15]^d[16]^d[19]^d[20]^d[22]^d[23]^d[25]^d[27]^d[28]^d[29]^d[31]^d[34]^d[38]^d[40]^d[41]^d[43]^d[45]^d[50]^d[51]^d[52]^d[54]^d[55]^d[56]^d[57]^d[58]^d[60]^d[61]^d[63]^c[2]^c[3]^c[4]^c[6]^c[7]^c[8]^c[9]^c[10]^c[12]^c[13]^c[15];
   assign c_nxt[9] = d[4]^d[8]^d[9]^d[12]^d[13]^d[15]^d[16]^d[17]^d[20]^d[21]^d[23]^d[24]^d[26]^d[28]^d[29]^d[30]^d[32]^d[35]^d[39]^d[41]^d[42]^d[44]^d[46]^d[51]^d[52]^d[53]^d[55]^d[56]^d[57]^d[58]^d[59]^d[61]^d[62]^c[3]^c[4]^c[5]^c[7]^c[8]^c[9]^c[10]^c[11]^c[13]^c[14];
   assign c_nxt[10] = d[5]^d[9]^d[10]^d[13]^d[14]^d[16]^d[17]^d[18]^d[21]^d[22]^d[24]^d[25]^d[27]^d[29]^d[30]^d[31]^d[33]^d[36]^d[40]^d[42]^d[43]^d[45]^d[47]^d[52]^d[53]^d[54]^d[56]^d[57]^d[58]^d[59]^d[60]^d[62]^d[63]^c[4]^c[5]^c[6]^c[8]^c[9]^c[10]^c[11]^c[12]^c[14]^c[15];
   assign c_nxt[11] = d[6]^d[10]^d[11]^d[14]^d[15]^d[17]^d[18]^d[19]^d[22]^d[23]^d[25]^d[26]^d[28]^d[30]^d[31]^d[32]^d[34]^d[37]^d[41]^d[43]^d[44]^d[46]^d[48]^d[53]^d[54]^d[55]^d[57]^d[58]^d[59]^d[60]^d[61]^d[63]^c[0]^c[5]^c[6]^c[7]^c[9]^c[10]^c[11]^c[12]^c[13]^c[15];
   assign c_nxt[12] = d[0]^d[4]^d[7]^d[8]^d[15]^d[16]^d[18]^d[22]^d[23]^d[24]^d[28]^d[29]^d[31]^d[38]^d[44]^d[45]^d[47]^d[48]^d[51]^d[52]^d[54]^d[59]^d[60]^d[61]^d[62]^d[63]^c[0]^c[3]^c[4]^c[6]^c[11]^c[12]^c[13]^c[14]^c[15];
   assign c_nxt[13] = d[1]^d[5]^d[8]^d[9]^d[16]^d[17]^d[19]^d[23]^d[24]^d[25]^d[29]^d[30]^d[32]^d[39]^d[45]^d[46]^d[48]^d[49]^d[52]^d[53]^d[55]^d[60]^d[61]^d[62]^d[63]^c[0]^c[1]^c[4]^c[5]^c[7]^c[12]^c[13]^c[14]^c[15];
   assign c_nxt[14] = d[2]^d[6]^d[9]^d[10]^d[17]^d[18]^d[20]^d[24]^d[25]^d[26]^d[30]^d[31]^d[33]^d[40]^d[46]^d[47]^d[49]^d[50]^d[53]^d[54]^d[56]^d[61]^d[62]^d[63]^c[1]^c[2]^c[5]^c[6]^c[8]^c[13]^c[14]^c[15];
   assign c_nxt[15] = d[3]^d[7]^d[10]^d[11]^d[18]^d[19]^d[21]^d[25]^d[26]^d[27]^d[31]^d[32]^d[34]^d[41]^d[47]^d[48]^d[50]^d[51]^d[54]^d[55]^d[57]^d[62]^d[63]^c[0]^c[2]^c[3]^c[6]^c[7]^c[9]^c[14]^c[15];


endmodule  // qeciphy_crc16_ibm3740
