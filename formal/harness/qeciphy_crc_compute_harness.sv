// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_crc_compute_harness;

   logic        clk_i;
   logic        rst_n_i;
   logic        faw_boundary_i;
   logic        crc_boundary_i;
   logic [63:0] tdata_i;

   logic [15:0] crc01_o, crc23_o, crc45_o;
   logic [7:0] crcvw_o;
   logic crc_valid_o;

   qeciphy_crc_compute dut (.*);

   // Input Assumptions

   // CRC boundary occurs after every 6 data packets
   sequence s_realistic_crc_boundary; (!faw_boundary_i && !crc_boundary_i) [* 6] ##1
    (!faw_boundary_i && crc_boundary_i); endsequence

   // FAW boundary occurs every 64 packets
   sequence s_realistic_faw_crc_boundary; (faw_boundary_i && !crc_boundary_i) [* 1] ##1 s_realistic_crc_boundary [* 9] ##1
    (faw_boundary_i && !crc_boundary_i) [* 1]; endsequence

   property realistic_faw_crc_boundary_sequence;
      @(posedge clk_i) disable iff (!rst_n_i) faw_boundary_i |-> s_realistic_faw_crc_boundary;
   endproperty

   realistic_faw_crc_boundary_sequence_A :
   assume property (realistic_faw_crc_boundary_sequence);

   logic faw_boundary_seen_t;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_boundary_seen_t <= 1'b0;
      end else if (faw_boundary_i) begin
         faw_boundary_seen_t <= 1'b1;
      end
   end

   // No CRC boundary should occur before the first FAW boundary
   property no_crc_boundary_until_first_faw_boundary;
      @(posedge clk_i) disable iff (!rst_n_i) !faw_boundary_seen_t |-> !crc_boundary_i;
   endproperty

   no_crc_boundary_until_first_faw_boundary_A :
   assume property (no_crc_boundary_until_first_faw_boundary);

endmodule
