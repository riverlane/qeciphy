// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_tx_boundary_gen_checker (
    input logic clk_i,
    input logic rst_n_i,
    input logic faw_boundary_o,
    input logic almost_faw_boundary_o,
    input logic crc_boundary_o
);

   // CRC boundary occurs after every 6 data packets
   sequence s_realistic_crc_boundary; (!faw_boundary_o && !crc_boundary_o) [* 6] ##1
    (!faw_boundary_o && crc_boundary_o); endsequence

   // FAW boundary occurs every 64 packets
   sequence s_realistic_faw_crc_boundary; (faw_boundary_o && !crc_boundary_o) [* 1] ##1 s_realistic_crc_boundary [* 9] ##1
    (faw_boundary_o && !crc_boundary_o) [* 1]; endsequence

   // Realistic FAW and CRC boundary sequence
   property p_realistic_faw_crc_boundary_sequence;
      @(posedge clk_i) disable iff (!rst_n_i) faw_boundary_o |-> s_realistic_faw_crc_boundary;
   endproperty

   p_realistic_faw_crc_boundary_sequence_A :
   assert property (p_realistic_faw_crc_boundary_sequence)
   else $fatal(1, "Unrealistic FAW/CRC boundary sequence at %m");

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

   // almost_faw_boundary_o should precede faw_boundary_o by one cycle
   property almost_faw_boundary_timing;
      @(posedge clk_i) disable iff (!rst_n_i) faw_boundary_o |-> $past(
          almost_faw_boundary_o, 1
      );
   endproperty

   almost_faw_boundary_timing_A :
   assert property (almost_faw_boundary_timing)
   else $fatal(1, "almost_faw_boundary_o timing violation at %m");

endmodule
