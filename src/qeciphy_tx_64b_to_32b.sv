// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// TX 64-bit to 32-bit Data Width Converter
//------------------------------------------------------------------------------
// This module converts 64-bit data to 32-bit data by 
// serializing the 64-bit input into two 32-bit output words.
//
// Operation:
// - Input: 64-bit data at half the output clock rate
// - Output: 32-bit data at full clock rate (2x faster than input)
// - Uses a toggle counter to alternate between lower and upper 32-bit words
// - Cycle 0: Output lower 32 bits [31:0]
// - Cycle 1: Output upper 32 bits [63:32]
//
// Timing:
// - Input clock rate is assumed to be half the output clock rate
// - No handshaking - assumes input data is always valid
//------------------------------------------------------------------------------

module qeciphy_tx_64b_to_32b (
    input  logic        clk_i,               // Clock input
    input  logic        rst_n_i,             // Active-low reset
    input  logic [63:0] tdata_64b_i,         // 64-bit input data at half the clock rate
    input  logic        tdata_64b_isfaw_i,   // Input indicates if tdata_64b is FAW
    output logic [31:0] tdata_32b_o,         // 32-bit output data at full clock rate
    output logic [ 3:0] tdata_32b_charisk_o  // tdata_32b character/isK indicators
);

   logic cycle;  // Toggle signal to select between lower/upper 32-bit words

   // Generate alternating cycle signal for word selection
   always_ff @(posedge clk_i) begin
      if (~rst_n_i) begin
         cycle <= 1'b0;
      end else begin
         cycle <= ~cycle;
      end
   end

   // Multiplex between lower and upper 32-bit words based on cycle
   always_ff @(posedge clk_i) begin
      if (~cycle) begin
         tdata_32b_o <= tdata_64b_i[31:0];  // Cycle 0: Output lower 32 bits
      end else begin
         tdata_32b_o <= tdata_64b_i[63:32];  // Cycle 1: Output upper 32 bits
      end
   end

   // Generate character/isK indicators for 32-bit output
   always_ff @(posedge clk_i) begin
      if (~rst_n_i) begin
         tdata_32b_charisk_o <= 4'b0000;
      end else if (~cycle && tdata_64b_isfaw_i) begin
         tdata_32b_charisk_o <= 4'b0001;  // Cycle 0: Lower 32 bits FAW contains K-character
      end else begin
         tdata_32b_charisk_o <= 4'b0000;
      end
   end

endmodule  // qeciphy_tx_64b_to_32b
