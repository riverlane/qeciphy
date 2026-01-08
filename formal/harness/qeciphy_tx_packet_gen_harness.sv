// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_tx_packet_gen_harness;

   logic        clk_i;
   logic        rst_n_i;
   logic        faw_boundary_i;
   logic        crc_boundary_i;
   logic [63:0] s_axis_tdata_i;
   logic        s_axis_tvalid_i;
   logic        s_axis_tready_o;
   logic [63:0] m_axis_tdata_o;
   logic        tx_off_i;
   logic        tx_idle_i;
   logic        tx_active_i;
   logic        rx_rdy_i;

   qeciphy_tx_packet_gen dut (.*);

   // Input Assumptions

   // tx_off_i, tx_idle_i, tx_active_i are one-hot
   property p_off_idle_active_onehot;
      @(posedge clk_i) disable iff (!rst_n_i) (tx_off_i + tx_idle_i + tx_active_i) == 1;
   endproperty

   p_off_idle_active_onehot_A :
   assume property (p_off_idle_active_onehot);

   // tx_off_i, tx_idle_i, tx_active_i remain stable between faw boundaries
   property p_off_idle_active_stable_between_faw_boundaries;
      @(posedge clk_i) disable iff (!rst_n_i) !faw_boundary_i |-> $stable(
          tx_off_i
      ) && $stable(
          tx_idle_i
      ) && $stable(
          tx_active_i
      );
   endproperty

   p_off_idle_active_stable_between_faw_boundaries_A :
   assume property (p_off_idle_active_stable_between_faw_boundaries);

   // s_axis_tvalid_i remains asserted until s_axis_tready_o is high
   property p_tvalid_asserted_until_ready;
      @(posedge clk_i) disable iff (!rst_n_i) s_axis_tvalid_i |-> s_axis_tvalid_i until s_axis_tready_o;
   endproperty

   p_tvalid_asserted_until_ready_A :
   assume property (p_tvalid_asserted_until_ready);

   // CRC boundary occurs after every 6 data packets
   sequence s_realistic_crc_boundary; (!faw_boundary_i && !crc_boundary_i) [* 6] ##1
    (!faw_boundary_i && crc_boundary_i); endsequence

   // FAW boundary occurs every 64 packets
   sequence s_realistic_faw_crc_boundary; (faw_boundary_i && !crc_boundary_i) [* 1] ##1 s_realistic_crc_boundary [* 9] ##1
    (faw_boundary_i && !crc_boundary_i) [* 1]; endsequence

   property p_realistic_faw_crc_boundary_sequence;
      @(posedge clk_i) disable iff (!rst_n_i) faw_boundary_i |-> s_realistic_faw_crc_boundary;
   endproperty

   p_realistic_faw_crc_boundary_sequence_A :
   assume property (p_realistic_faw_crc_boundary_sequence);

   // Track if FAW boundary has been seen
   logic faw_boundary_seen_t;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_boundary_seen_t <= 1'b0;
      end else if (faw_boundary_i) begin
         faw_boundary_seen_t <= 1'b1;
      end
   end

   // No CRC boundary should occur before the first FAW boundary
   property p_no_crc_boundary_until_first_faw_boundary;
      @(posedge clk_i) disable iff (!rst_n_i) !faw_boundary_seen_t |-> !crc_boundary_i;
   endproperty

   p_no_crc_boundary_until_first_faw_boundary_A :
   assume property (p_no_crc_boundary_until_first_faw_boundary);

endmodule
