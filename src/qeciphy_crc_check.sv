// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// CRC Validation Checker
//------------------------------------------------------------------------------
// This module validates calculated CRC values against expected values contained
// in a validation packet received during CRC boundary cycles.
//
// Operation:
// - Captures validation packet from tdata_i when crc_boundary_i is asserted
// - Compares calculated CRC values (crc01_i, crc23_i, crc45_i, crcvw_i) against
//   expected values from the validation packet
// - Performs byte-wise comparison for 16-bit CRC values to reduce combinational load
// - Generates an error signal if any CRC comparison fails
// - Uses 2-cycle pipeline
//------------------------------------------------------------------------------

`include "qeciphy_pkg.sv"

module qeciphy_crc_check (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic        crc_boundary_i,
    input  logic [63:0] tdata_i,
    input  logic [15:0] crc01_i,
    input  logic [15:0] crc23_i,
    input  logic [15:0] crc45_i,
    input  logic [ 7:0] crcvw_i,
    input  logic        crc_valid_i,
    output logic        crc_error_o,
    output logic        check_done_o
);

   import qeciphy_pkg::*;

   qeciphy_vd_pkt_t       vd_pkt;  // Validation packet format
   logic                  crc01_byte_match                                     [0:1];  // Per-byte match results for CRC01
   logic                  crc23_byte_match                                     [0:1];  // Per-byte match results for CRC23  
   logic                  crc45_byte_match                                     [0:1];  // Per-byte match results for CRC45
   logic                  crcvw_match;  // Match result for CRC validation word
   logic            [1:0] valid_pipe;  // Valid signal pipeline for timing
   logic                  crc_error;  // Internal error signal

   assign check_done_o = valid_pipe[1];  // Completion after pipeline delay

   // Valid signal pipeline
   always_ff @(posedge clk_i or negedge rst_n_i) begin
      if (!rst_n_i) valid_pipe <= 2'h0;
      else valid_pipe <= {valid_pipe[0], crc_valid_i};
   end

   // Store expected CRC values on boundary
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         vd_pkt <= '0;
      end else if (crc_boundary_i) begin
         vd_pkt <= qeciphy_vd_pkt_t'(tdata_i);  // Cast input data to validation packet type
      end
   end

   // Check calculated vs expected values byte-wise
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc01_byte_match[0] <= 1'b0;
         crc01_byte_match[1] <= 1'b0;
         crc23_byte_match[0] <= 1'b0;
         crc23_byte_match[1] <= 1'b0;
         crc45_byte_match[0] <= 1'b0;
         crc45_byte_match[1] <= 1'b0;
         crcvw_match    <= 1'b0;
      end else if (crc_valid_i) begin
         // Compare each byte of 16-bit CRC values
         crc01_byte_match[0] <= (vd_pkt.crc01[7:0] == crc01_i[7:0]);
         crc01_byte_match[1] <= (vd_pkt.crc01[15:8] == crc01_i[15:8]);
         crc23_byte_match[0] <= (vd_pkt.crc23[7:0] == crc23_i[7:0]);
         crc23_byte_match[1] <= (vd_pkt.crc23[15:8] == crc23_i[15:8]);
         crc45_byte_match[0] <= (vd_pkt.crc45[7:0] == crc45_i[7:0]);
         crc45_byte_match[1] <= (vd_pkt.crc45[15:8] == crc45_i[15:8]);
         crcvw_match    <= (vd_pkt.crcvw == crcvw_i);  // Single byte comparison
      end
   end

   assign crc_error_o = crc_error;

   // Error signal generation
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_error <= 1'b0;
      end else if (valid_pipe[0]) begin
         // Set error if any CRC comparison fails
         crc_error <= ~((crc01_byte_match[0] && crc01_byte_match[1]) && (crc23_byte_match[0] && crc23_byte_match[1]) && (crc45_byte_match[0] && crc45_byte_match[1]) && crcvw_match);
      end
   end

endmodule
