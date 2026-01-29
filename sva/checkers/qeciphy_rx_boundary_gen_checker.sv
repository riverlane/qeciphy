// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_rx_boundary_gen_checker (
    input logic        clk_i,
    input logic        rst_n_i,
    input logic [63:0] tdata_i,
    input logic [63:0] tdata_o,
    input logic        enable_i,
    input logic        locked_o,
    input logic        faw_boundary_o,
    input logic        crc_boundary_o
);

   import qeciphy_pkg::*;

   localparam FAW_TO_LOCKED_LATENCY = 4;
   localparam FAW_DISTANCE = 64;

   // Calculate past offsets for FAW checks from locked assertion
   localparam P0 = FAW_TO_LOCKED_LATENCY + 0 * FAW_DISTANCE;
   localparam P1 = FAW_TO_LOCKED_LATENCY + 1 * FAW_DISTANCE;
   localparam P2 = FAW_TO_LOCKED_LATENCY + 2 * FAW_DISTANCE;
   localparam P3 = FAW_TO_LOCKED_LATENCY + 3 * FAW_DISTANCE;
   localparam P4 = FAW_TO_LOCKED_LATENCY + 4 * FAW_DISTANCE;
   localparam P5 = FAW_TO_LOCKED_LATENCY + 5 * FAW_DISTANCE;
   localparam P6 = FAW_TO_LOCKED_LATENCY + 6 * FAW_DISTANCE;
   localparam P7 = FAW_TO_LOCKED_LATENCY + 7 * FAW_DISTANCE;

   // Ensure that locked_o is rechable
   cover_locked_o_C :
   cover property (@(posedge clk_i) locked_o);

   // Once locked_o is asserted, it remains asserted as long as enable_i is high
   property p_locked_stays_locked;
      @(posedge clk_i) disable iff (!rst_n_i) (locked_o && enable_i) |-> ##1 (locked_o);
   endproperty

   p_locked_stays_locked_A :
   assert property (p_locked_stays_locked)
   else $fatal(1, "locked_o deasserted unexpectedly at %m");

   // When enable_i is low, locked_o, faw_boundary_o, and crc_boundary_o should all be low
   property p_disable_clears_outputs;
      @(posedge clk_i) disable iff (!rst_n_i) !enable_i |-> ##1 !locked_o && !faw_boundary_o && !crc_boundary_o;
   endproperty

   p_disable_clears_outputs_A :
   assert property (p_disable_clears_outputs)
   else $fatal(1, "Outputs not cleared on disable at %m");

   // CRC boundary occurs after every 6 data packets
   sequence s_realistic_crc_boundary; (!faw_boundary_o && !crc_boundary_o) [* 6] ##1
    (!faw_boundary_o && crc_boundary_o); endsequence

   // FAW boundary occurs every 64 packets
   sequence s_realistic_faw_crc_boundary; (faw_boundary_o && !crc_boundary_o) [* 1] ##1 s_realistic_crc_boundary [* 9] ##1
    (faw_boundary_o && !crc_boundary_o) [* 1]; endsequence

   // Realistic FAW and CRC boundary sequence
   property p_realistic_faw_crc_boundary_sequence;
      @(posedge clk_i) disable iff (!rst_n_i || !enable_i) faw_boundary_o |-> s_realistic_faw_crc_boundary;
   endproperty

   p_realistic_faw_crc_boundary_sequence_A :
   assert property (p_realistic_faw_crc_boundary_sequence)
   else $fatal(1, "Unrealistic FAW/CRC boundary sequence at %m");

   // No FAW or CRC boundary should occur when not locked
   property p_no_faw_crc_boundary_when_unlocked;
      @(posedge clk_i) disable iff (!rst_n_i) !locked_o |-> !crc_boundary_o && !faw_boundary_o;
   endproperty

   p_no_faw_crc_boundary_when_unlocked_A :
   assert property (p_no_faw_crc_boundary_when_unlocked)
   else $fatal(1, "FAW/CRC boundary asserted when unlocked at %m");

   // Track if first FAW boundary has been seen
   logic faw_boundary_seen_t;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_boundary_seen_t <= 1'b0;
      end else if (faw_boundary_o) begin
         faw_boundary_seen_t <= 1'b1;
      end
   end

   // No CRC boundary should occur before the first FAW boundary
   property p_no_crc_boundary_until_first_faw_boundary;
      @(posedge clk_i) disable iff (!rst_n_i) !faw_boundary_seen_t |-> !crc_boundary_o;
   endproperty

   p_no_crc_boundary_until_first_faw_boundary_A :
   assert property (p_no_crc_boundary_until_first_faw_boundary)
   else $fatal(1, "CRC boundary occurred before first FAW boundary at %m");

   // No spurious locked_o assertions
   // locked_o assertion must be preceded by 8 correct FAW patterns at minimum
   // One for alignment and seven for checking
   property p_no_spurious_locked;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          locked_o
      ) |-> $past(
          is_faw(tdata_i), P0
      ) && $past(
          is_faw(tdata_i), P1
      ) && $past(
          is_faw(tdata_i), P2
      ) && $past(
          is_faw(tdata_i), P3
      ) && $past(
          is_faw(tdata_i), P4
      ) && $past(
          is_faw(tdata_i), P5
      ) && $past(
          is_faw(tdata_i), P6
      ) && $past(
          is_faw(tdata_i), P7
      );
   endproperty

   p_no_spurious_locked_A :
   assert property (p_no_spurious_locked)
   else $fatal(1, "Spurious locked_o assertion at %m");

   // If there are 8 correct FAW patterns spaced FAW_DISTANCE apart,
   // and no FAW patterns in between, then locked_o must be asserted
   property p_locked_correctness;
      @(posedge clk_i) disable iff (!rst_n_i || !enable_i) enable_i throughout (!is_faw(
          tdata_i
      ) [* (FAW_DISTANCE - 1)] ##1 is_faw(
          tdata_i
      ) ##1 !is_faw(
          tdata_i
      ) [* (FAW_DISTANCE - 1)] ##1 is_faw(
          tdata_i
      ) ##1 !is_faw(
          tdata_i
      ) [* (FAW_DISTANCE - 1)] ##1 is_faw(
          tdata_i
      ) ##1 !is_faw(
          tdata_i
      ) [* (FAW_DISTANCE - 1)] ##1 is_faw(
          tdata_i
      ) ##1 !is_faw(
          tdata_i
      ) [* (FAW_DISTANCE - 1)] ##1 is_faw(
          tdata_i
      ) ##1 !is_faw(
          tdata_i
      ) [* (FAW_DISTANCE - 1)] ##1 is_faw(
          tdata_i
      ) ##1 !is_faw(
          tdata_i
      ) [* (FAW_DISTANCE - 1)] ##1 is_faw(
          tdata_i
      ) ##1 !is_faw(
          tdata_i
      ) [* (FAW_DISTANCE - 1)] ##1 is_faw(
          tdata_i
      ) ##1 !is_faw(
          tdata_i
      ) [* (FAW_DISTANCE - 1)]) |-> ##FAW_TO_LOCKED_LATENCY locked_o;
   endproperty

   locked_correctness_A :
   assert property (p_locked_correctness)
   else $fatal(1, "locked_o correctness failure at %m");

   // tdata_o should match tdata_i when enabled
   property p_tdata_o_correctness;
      @(posedge clk_i) disable iff (!rst_n_i || !enable_i) (tdata_o == tdata_i);
   endproperty

   tdata_o_correctness_A :
   assert property (p_tdata_o_correctness)
   else $fatal(1, "tdata_o correctness failure at %m");

endmodule
