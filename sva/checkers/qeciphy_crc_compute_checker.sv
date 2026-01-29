// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_crc_compute_checker (
    input logic        clk_i,
    input logic        rst_n_i,
    input logic        faw_boundary_i,
    input logic        crc_boundary_i,
    input logic [63:0] tdata_i,

    input logic crc01_rst_n,
    input logic crc23_rst_n,
    input logic crc45_rst_n,
    input logic crcvw_rst_n,

    input logic crc01_en,
    input logic crc23_en,
    input logic crc45_en,
    input logic crcvw_en,

    input logic crc01_valid,
    input logic crc23_valid,
    input logic crc45_valid,
    input logic crcvw_valid,

    input logic [15:0] crc01_calc,
    input logic [15:0] crc23_calc,
    input logic [15:0] crc45_calc,
    input logic [ 7:0] crcvw_calc,

    input logic crc_valid_o,
    input logic [15:0] crc01_o,
    input logic [15:0] crc23_o,
    input logic [15:0] crc45_o,
    input logic [7:0] crcvw_o
);

   localparam CRC01_VALID_TO_OUTPUT_VALID_LATENCY = 4;
   localparam CRC23_VALID_TO_OUTPUT_VALID_LATENCY = 2;
   localparam CRC45_VALID_TO_OUTPUT_VALID_LATENCY = 0;
   localparam CRCVW_VALID_TO_OUTPUT_VALID_LATENCY = 0;

   // At most one of the crc enables can be high at any clock cycle
   property p_crc_en_onehot;
      @(posedge clk_i) disable iff (!rst_n_i) $onehot0(
          {crc01_en, crc23_en, crc45_en, crcvw_en}
      );
   endproperty

   p_crc_en_onehot_A :
   assert property (p_crc_en_onehot)
   else $fatal(1, "CRC enable signals are not one-hot at %m");

   // crc_valid signals from the CRC modules and their corresponding rst_n signals are mutually exclusive
   // crc01
   property p_crc01_valid_rst_mutually_exclusive;
      @(posedge clk_i) disable iff (!rst_n_i) !(crc01_valid && !crc01_rst_n);
   endproperty

   p_crc01_valid_rst_mutually_exclusive_A :
   assert property (p_crc01_valid_rst_mutually_exclusive)
   else $fatal(1, "CRC01 valid and reset signals are not mutually exclusive at %m");

   // crc23
   property p_crc23_valid_rst_mutually_exclusive;
      @(posedge clk_i) disable iff (!rst_n_i) !(crc23_valid && !crc23_rst_n);
   endproperty

   p_crc23_valid_rst_mutually_exclusive_A :
   assert property (p_crc23_valid_rst_mutually_exclusive)
   else $fatal(1, "CRC23 valid and reset signals are not mutually exclusive at %m");

   // crc45
   property p_crc45_valid_rst_mutually_exclusive;
      @(posedge clk_i) disable iff (!rst_n_i) !(crc45_valid && !crc45_rst_n);
   endproperty

   p_crc45_valid_rst_mutually_exclusive_A :
   assert property (p_crc45_valid_rst_mutually_exclusive)
   else $fatal(1, "CRC45 valid and reset signals are not mutually exclusive at %m");

   // crcvw
   property p_crcvw_valid_rst_mutually_exclusive;
      @(posedge clk_i) disable iff (!rst_n_i) !(crcvw_valid && !crcvw_rst_n);
   endproperty

   p_crcvw_valid_rst_mutually_exclusive_A :
   assert property (p_crcvw_valid_rst_mutually_exclusive)
   else $fatal(1, "CRCVW valid and reset signals are not mutually exclusive at %m");

   // CRC enable signals should be asserted and deasserted at correct times around FAW boundary
   property p_correct_enable_timing_around_faw_boundary;
      @(posedge clk_i) disable iff (!rst_n_i) faw_boundary_i |-> (!crc01_en && !crc23_en && !crc45_en && !crcvw_en);
   endproperty

   p_correct_enable_timing_around_faw_boundary_A :
   assert property (p_correct_enable_timing_around_faw_boundary)
   else $fatal(1, "CRC enable signals timing around FAW boundary incorrect at %m");

   // CRC enable signals should be asserted and deasserted at correct times around CRC boundary
   property p_correct_enable_timing_around_crc_boundary;
      @(posedge clk_i) disable iff (!rst_n_i) crc_boundary_i |-> (!crc01_en && !crc23_en && !crc45_en && crcvw_en) && $past(
          !crc01_en && !crc23_en && crc45_en && !crcvw_en, 1
      ) && $past(
          !crc01_en && !crc23_en && crc45_en && !crcvw_en, 2
      ) && $past(
          !crc01_en && crc23_en && !crc45_en && !crcvw_en, 3
      ) && $past(
          !crc01_en && crc23_en && !crc45_en && !crcvw_en, 4
      ) && $past(
          crc01_en && !crc23_en && !crc45_en && !crcvw_en, 5
      ) && $past(
          crc01_en && !crc23_en && !crc45_en && !crcvw_en, 6
      );
   endproperty

   p_correct_enable_timing_around_crc_boundary_A :
   assert property (p_correct_enable_timing_around_crc_boundary)
   else $fatal(1, "CRC enable signals timing around CRC boundary incorrect at %m");

   // Track if first FAW boundary has been seen
   logic first_faw_seen_t;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         first_faw_seen_t <= 1'b0;
      end else if (faw_boundary_i) begin
         first_faw_seen_t <= 1'b1;
      end
   end

   // CRC reset signals should be asserted and deasserted at correct times around FAW boundary
   property p_correct_reset_timing_around_faw_boundary;
      @(posedge clk_i) disable iff (!rst_n_i) first_faw_seen_t && faw_boundary_i |-> (crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n);
   endproperty

   p_correct_reset_timing_around_faw_boundary_A :
   assert property (p_correct_reset_timing_around_faw_boundary)
   else $fatal(1, "CRC reset signals timing around FAW boundary incorrect at %m");

   // CRC reset signals should be asserted and deasserted at correct times around CRC boundary
   property p_correct_reset_timing_around_crc_boundary;
      @(posedge clk_i) disable iff (!rst_n_i) crc_boundary_i |-> (crc01_rst_n && !crc23_rst_n && crc45_rst_n && crcvw_rst_n) && $past(
          crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n, 1
      ) && $past(
          !crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n, 2
      ) && $past(
          crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n, 3
      ) && $past(
          crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n, 4
      ) && $past(
          crc01_rst_n && crc23_rst_n && !crc45_rst_n && !crcvw_rst_n, 5
      ) && $past(
          crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n, 6
      );
   endproperty

   p_correct_reset_timing_around_crc_boundary_A :
   assert property (p_correct_reset_timing_around_crc_boundary)
   else $fatal(1, "CRC reset signals timing around CRC boundary incorrect at %m");

   // Output CRC values must match calculated values when crc_valid_o is asserted
   property p_correct_crc_output_values;
      @(posedge clk_i) disable iff (!rst_n_i) crc_valid_o |-> ((crc01_o == $past(
          crc01_calc, CRC01_VALID_TO_OUTPUT_VALID_LATENCY
      )) && (crc23_o == $past(
          crc23_calc, CRC23_VALID_TO_OUTPUT_VALID_LATENCY
      )) && (crc45_o == crc45_calc) && (crcvw_o == crcvw_calc));
   endproperty

   p_correct_crc_output_values_A :
   assert property (p_correct_crc_output_values)
   else $fatal(1, "CRC output values incorrect at %m");

   // crc_valid_o should only be asserted when a CRC boundary occurs
   property p_no_spurious_crc_valid_o;
      @(posedge clk_i) disable iff (!rst_n_i) crc_valid_o |-> $past(
          crc_boundary_i
      );
   endproperty

   p_no_spurious_crc_valid_o_A :
   assert property (p_no_spurious_crc_valid_o)
   else $fatal(1, "Spurious crc_valid_o assertion at %m");

   // crc_valid_o should be asserted one cycle after crc_boundary_i
   property p_crc_valid_o_timing;
      @(posedge clk_i) disable iff (!rst_n_i) crc_boundary_i |-> ##1 crc_valid_o;
   endproperty

   p_crc_valid_o_timing_A :
   assert property (p_crc_valid_o_timing)
   else $fatal(1, "crc_valid_o timing incorrect at %m");

   // Ensure crc_valid_o is reachable
   cover_crc_valid_o_C :
   cover property (@(posedge clk_i) crc_valid_o);

endmodule
