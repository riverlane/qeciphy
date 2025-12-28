// SPDX-License-Identifier: LicenseRef-LICENSE
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

   // At most one of the crc enables can be high at any clock cycle
   property p_crc_en_onehot;
      @(posedge clk_i) disable iff (!rst_n_i) $onehot0(
          {crc01_en, crc23_en, crc45_en, crcvw_en}
      );
   endproperty

   p_crc_en_onehot_A :
   assert property (p_crc_en_onehot);

   // crc_valid signals from the CRC modules and their corresponding rst_n signals are mutually exclusive
   // crc01
   property p_crc01_valid_rst_mutually_exclusive;
      @(posedge clk_i) disable iff (!rst_n_i) !(crc01_valid && !crc01_rst_n);
   endproperty

   p_crc01_valid_rst_mutually_exclusive_A :
   assert property (p_crc01_valid_rst_mutually_exclusive);

   // crc23
   property p_crc23_valid_rst_mutually_exclusive;
      @(posedge clk_i) disable iff (!rst_n_i) !(crc23_valid && !crc23_rst_n);
   endproperty

   p_crc23_valid_rst_mutually_exclusive_A :
   assert property (p_crc23_valid_rst_mutually_exclusive);

   // crc45
   property p_crc45_valid_rst_mutually_exclusive;
      @(posedge clk_i) disable iff (!rst_n_i) !(crc45_valid && !crc45_rst_n);
   endproperty

   p_crc45_valid_rst_mutually_exclusive_A :
   assert property (p_crc45_valid_rst_mutually_exclusive);

   // crcvw
   property p_crcvw_valid_rst_mutually_exclusive;
      @(posedge clk_i) disable iff (!rst_n_i) !(crcvw_valid && !crcvw_rst_n);
   endproperty

   p_crcvw_valid_rst_mutually_exclusive_A :
   assert property (p_crcvw_valid_rst_mutually_exclusive);

   // Check correct timing of crc enables with respect to FAW and CRC boundaries
   sequence s_correct_enable_timing_upto_crc_boundary;
      ( !crc_boundary_i && crc01_en && !crc23_en && !crc45_en && !crcvw_en) [* 2] ##1
        ( !crc_boundary_i && !crc01_en && crc23_en && !crc45_en && !crcvw_en) [* 2] ##1
        ( !crc_boundary_i && !crc01_en && !crc23_en && crc45_en && !crcvw_en) [* 2] ##1
        ( crc_boundary_i && !crc01_en && !crc23_en && !crc45_en && crcvw_en);
   endsequence

   sequence s_correct_enable_timing_from_faw_boundary;
      (faw_boundary_i && !crc_boundary_i && !crc01_en && !crc23_en && !crc45_en && !crcvw_en) ##1 s_correct_enable_timing_upto_crc_boundary [* 1: $];
   endsequence

   property p_correct_enable_timing_from_faw_boundary;
      @(posedge clk_i) disable iff (!rst_n_i) faw_boundary_i |-> s_correct_enable_timing_from_faw_boundary;
   endproperty

   p_correct_enable_timing_from_faw_boundary_A :
   assert property (p_correct_enable_timing_from_faw_boundary);

   // Check correct timing of crc resets with respect to FAW and CRC boundaries
   sequence s_correct_crc_rst_timing_upto_crc_boundary;
      ( !crc_boundary_i && crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n) ##1
        ( !crc_boundary_i && crc01_rst_n && crc23_rst_n && !crc45_rst_n && !crcvw_rst_n) ##1
        ( !crc_boundary_i && crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n) [* 2] ##1
        ( !crc_boundary_i && !crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n) ##1
        ( !crc_boundary_i && crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n) ##1
        ( crc_boundary_i && crc01_rst_n && !crc23_rst_n && crc45_rst_n && crcvw_rst_n);
   endsequence

   sequence s_correct_crc_rst_timing_from_faw_boundary;
      (faw_boundary_i && !crc_boundary_i && crc01_rst_n && crc23_rst_n && crc45_rst_n && crcvw_rst_n) ##1 s_correct_crc_rst_timing_upto_crc_boundary [* 1: $];
   endsequence

   property p_correct_crc_rst_timing_from_faw_boundary;
      @(posedge clk_i) disable iff (!rst_n_i) faw_boundary_i |-> s_correct_crc_rst_timing_from_faw_boundary;
   endproperty

   p_correct_crc_rst_timing_from_faw_boundary_A :
   assert property (p_correct_crc_rst_timing_from_faw_boundary);

   // Uutput CRC values must match calculated values when crc_valid_o is asserted
   property p_correct_crc_output_values;
      @(posedge clk_i) disable iff (!rst_n_i) crc_valid_o |-> ((crc01_o == $past(
          crc01_calc, 4
      )) && (crc23_o == $past(
          crc23_calc, 2
      )) && (crc45_o == crc45_calc) && (crcvw_o == crcvw_calc));
   endproperty

   p_correct_crc_output_values_A :
   assert property (p_correct_crc_output_values);


   // Ensure crc_valid_o is reachable
   cover_crc_valid_o_C :
   cover property (@(posedge clk_i) crc_valid_o);

endmodule
