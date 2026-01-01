// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

`include "src/qeciphy_pkg.sv"

module qeciphy_rx_monitor_checker (
    input logic clk_i,
    input logic rst_n_i,

    input logic [63:0] tdata_i,

    input logic [63:0] tdata_o,
    input logic        tvalid_o,

    input logic enable_i,
    input logic faw_boundary_i,
    input logic crc_boundary_i,

    input logic crc_error_o,
    input logic faw_error_o,
    input logic remote_rx_rdy_o,

    input logic crc_check_done,
    input logic crc_check_error
);

   import qeciphy_pkg::*;

   localparam FIRST_DATA_IN_TO_CRC_BOUNDARY_LATENCY = 6;
   localparam CRC_BOUNDARY_TO_CHECK_DONE_LATENCY = 3;
   localparam CHECK_DONE_TO_FIRST_DATA_OUT_LATENCY = 2;
   localparam CRC_BOUNDARY_TO_FIRST_DATA_OUT_LATENCY = CRC_BOUNDARY_TO_CHECK_DONE_LATENCY + CHECK_DONE_TO_FIRST_DATA_OUT_LATENCY;
   localparam TOTAL_DATA_PATH_LATENCY = FIRST_DATA_IN_TO_CRC_BOUNDARY_LATENCY + CRC_BOUNDARY_TO_FIRST_DATA_OUT_LATENCY;

   // Ensure faw_error_o is reachable
   cover_faw_error_o_C :
   cover property (@(posedge clk_i) faw_error_o);

   // Ensure crc_error_o is reachable
   cover_crc_error_o_C :
   cover property (@(posedge clk_i) crc_error_o);

   // Ensure remote_rx_rdy_o is reachable
   cover_remote_rx_rdy_o_C :
   cover property (@(posedge clk_i) remote_rx_rdy_o);

   // Ensure tvalid_o is reachable
   cover_tvalid_o_C :
   cover property (@(posedge clk_i) tvalid_o);

   // crc_error_o can only be raised when qeciphy_crc_check module indicates an error
   property p_no_spurious_crc_error;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          crc_error_o
      ) |-> $past(
          crc_check_error && crc_check_done && enable_i
      );
   endproperty

   no_spurious_crc_error_A :
   assert property (p_no_spurious_crc_error)
   else $fatal(1, "Spurious crc_error_o at %m");

   // crc_error_o should be asserted whenever qeciphy_crc_check module indicates an error
   property p_crc_error_correctness;
      @(posedge clk_i) disable iff (!rst_n_i) (crc_check_done && crc_check_error && enable_i) |-> ##1 crc_error_o;
   endproperty

   crc_error_correctness_A :
   assert property (p_crc_error_correctness)
   else $fatal(1, "crc_error_o incorrect at %m");

   // crc_error_o sticky until disabled
   property p_crc_error_sticky;
      @(posedge clk_i) disable iff (!rst_n_i) crc_error_o && enable_i |-> ##1 crc_error_o;
   endproperty

   crc_error_sticky_A :
   assert property (p_crc_error_sticky)
   else $fatal(1, "crc_error_o not sticky at %m");

   // faw_error_o is only raised on invalid FAW words
   property p_no_spurious_faw_error;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          faw_error_o
      ) |-> $past(
          !is_faw(tdata_i) && faw_boundary_i && enable_i
      );
   endproperty

   no_spurious_faw_error_A :
   assert property (p_no_spurious_faw_error)
   else $fatal(1, "Spurious faw_error_o at %m");

   // faw_error_o must be asserted whenever there is an invalid FAW
   property p_faw_error_correctness;
      @(posedge clk_i) disable iff (!rst_n_i) faw_boundary_i && enable_i && !is_faw(
          tdata_i
      ) |-> ##1 faw_error_o;
   endproperty

   faw_error_correctness_A :
   assert property (p_faw_error_correctness)
   else $fatal(1, "faw_error_o incorrect at %m");

   // faw_error_o sticky until disabled
   property p_faw_error_sticky;
      @(posedge clk_i) disable iff (!rst_n_i) faw_error_o && enable_i |-> ##1 faw_error_o;
   endproperty

   faw_error_sticky_A :
   assert property (p_faw_error_sticky)
   else $fatal(1, "faw_error_o not sticky at %m");

   // remote_rx_rdy_o can only be raised when FAW indicates remote ready
   property p_no_spurious_remote_rx_rdy;
      qeciphy_faw_t faw_snap;
      @(posedge clk_i) disable iff (!rst_n_i) (1,
      faw_snap = qeciphy_faw_t'(tdata_i)
      ) ##1 $rose(
          remote_rx_rdy_o
      ) |-> $past(
          enable_i && faw_boundary_i
      ) && faw_snap.rx_rdy;
   endproperty

   no_spurious_remote_rx_rdy_A :
   assert property (p_no_spurious_remote_rx_rdy)
   else $fatal(1, "Spurious remote_rx_rdy_o at %m");

   // remote_rx_rdy_o must be asserted whenever FAW indicates remote ready
   property p_remote_rx_rdy_correctness;
      qeciphy_faw_t faw_snap;
      @(posedge clk_i) disable iff (!rst_n_i) (faw_boundary_i && enable_i,
      faw_snap = qeciphy_faw_t'(tdata_i)
      ) |-> ##1 (remote_rx_rdy_o == faw_snap.rx_rdy);
   endproperty

   remote_rx_rdy_correctness_A :
   assert property (p_remote_rx_rdy_correctness)
   else $fatal(1, "remote_rx_rdy_o incorrect at %m");

   // Disabling clears outputs
   property p_disable_clears_outputs;
      @(posedge clk_i) disable iff (!rst_n_i) !enable_i |-> ##1 (!crc_error_o && !faw_error_o && !remote_rx_rdy_o && !tvalid_o);
   endproperty

   disable_clears_outputs_A :
   assert property (p_disable_clears_outputs)
   else $fatal(1, "Disabling did not clear outputs at %m");

   // A boundary word must never be marked valid when it comes out
   property p_no_valid_on_boundary_words;
      @(posedge clk_i) disable iff (!rst_n_i) (crc_boundary_i || faw_boundary_i) |-> ##TOTAL_DATA_PATH_LATENCY !tvalid_o;
   endproperty

   no_valid_on_boundary_words_A :
   assert property (p_no_valid_on_boundary_words)
   else $fatal(1, "tvalid_o asserted on boundary word at %m");

   // No valid output after there is a CRC error
   property p_no_valid_from_crc_error;
      @(posedge clk_i) disable iff (!rst_n_i) crc_error_o |-> ##1 !tvalid_o;
   endproperty

   no_valid_from_crc_error_A :
   assert property (p_no_valid_from_crc_error)
   else $fatal(1, "tvalid_o asserted after crc_error_o at %m");

   // No valid output after there is a FAW error
   property p_no_valid_from_faw_error;
      @(posedge clk_i) disable iff (!rst_n_i) faw_error_o |-> ##1 !tvalid_o;
   endproperty

   no_valid_from_faw_error_A :
   assert property (p_no_valid_from_faw_error)
   else $fatal(1, "tvalid_o asserted after faw_error_o at %m");

   // tvalid_o resepects the valid bits in the validation packet
   property p_tvalid_respects_valid_bits;
      qeciphy_vd_pkt_t vd_pkt_snap;
      @(posedge clk_i) disable iff (!rst_n_i || !enable_i || faw_error_o || crc_error_o) (crc_boundary_i && enable_i,
      vd_pkt_snap = qeciphy_vd_pkt_t'(tdata_i)
      ) |-> ##CRC_BOUNDARY_TO_FIRST_DATA_OUT_LATENCY tvalid_o == vd_pkt_snap.valids[0] ##1 tvalid_o == vd_pkt_snap.valids[1] ##1 tvalid_o == vd_pkt_snap.valids[2] ##1 tvalid_o == vd_pkt_snap.valids[3]
          ##1 tvalid_o == vd_pkt_snap.valids[4] ##1 tvalid_o == vd_pkt_snap.valids[5];
   endproperty

   p_tvalid_respects_valid_bits_A :
   assert property (p_tvalid_respects_valid_bits)
   else $fatal(1, "tvalid_o does not respect valid bits at %m");

   // tdata_o matches input data (considering latency) when tvalid_o is asserted
   property p_tdata_o_matches_input_when_valid;
      @(posedge clk_i) disable iff (!rst_n_i) tvalid_o |-> tdata_o == $past(
          tdata_i, TOTAL_DATA_PATH_LATENCY
      );
   endproperty

   tdata_o_matches_input_when_valid_A :
   assert property (p_tdata_o_matches_input_when_valid)
   else $fatal(1, "tdata_o does not match input at %m");

endmodule
