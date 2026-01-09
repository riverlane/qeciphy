// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

`include "qeciphy_pkg.sv"

module qeciphy_crc_check_checker (
    input logic        clk_i,
    input logic        rst_n_i,
    input logic        crc_boundary_i,
    input logic [63:0] tdata_i,
    input logic [15:0] crc01_i,
    input logic [15:0] crc23_i,
    input logic [15:0] crc45_i,
    input logic [ 7:0] crcvw_i,
    input logic        crc_valid_i,
    input logic        crc_error_o,
    input logic        check_done_o
);

   import qeciphy_pkg::*;

   // Ensure check_done_o is reachable
   cover_check_done_o_C :
   cover property (@(posedge clk_i) check_done_o);

   // Ensure crc_error_o is reachable
   cover_crc_error_o_C :
   cover property (@(posedge clk_i) crc_error_o);

   // check_done_o is asserted 2 cycles after crc_valid_i following crc_boundary_i
   property p_check_done_delay;
      @(posedge clk_i) disable iff (!rst_n_i) crc_boundary_i |-> ##1 crc_valid_i ##2 check_done_o;
   endproperty

   p_check_done_delay_A :
   assert property (p_check_done_delay)
   else $fatal(1, "check_done_o timing violation at %m");

   // No spurious assertions of check_done_o
   property p_no_spurious_check_done;
      @(posedge clk_i) disable iff (!rst_n_i) check_done_o |-> $past(
          crc_valid_i, 2
      ) && $past(
          crc_boundary_i, 3
      );
   endproperty

   p_no_spurious_check_done_A :
   assert property (p_no_spurious_check_done)
   else $fatal(1, "Spurious check_done_o assertion at %m");

   // No spurious assertions of crc_error_o
   property p_no_spurious_crc_error;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          crc_error_o
      ) |-> check_done_o;
   endproperty

   p_no_spurious_crc_error_A :
   assert property (p_no_spurious_crc_error)
   else $fatal(1, "Spurious crc_error_o assertion at %m");

   // Capture the validation packet at crc boundary
   qeciphy_vd_pkt_t vd_pkt;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         vd_pkt <= '0;
      end else if (crc_boundary_i) begin
         vd_pkt = qeciphy_vd_pkt_t'(tdata_i);
      end
   end

   // Check correctness of crc_error_o signal
   property p_check_crc_error_correctness;
      @(posedge clk_i) disable iff (!rst_n_i) check_done_o && !$past(
          crc_error_o
      ) |-> (crc_error_o == ~(((vd_pkt.crc01 == $past(
          crc01_i, 2
      )) && (vd_pkt.crc23 == $past(
          crc23_i, 2
      )) && (vd_pkt.crc45 == $past(
          crc45_i, 2
      )) && (vd_pkt.crcvw == $past(
          crcvw_i, 2
      )))));
   endproperty

   p_check_crc_error_correctness_A :
   assert property (p_check_crc_error_correctness)
   else $fatal(1, "crc_error_o correctness violation at %m");

endmodule
