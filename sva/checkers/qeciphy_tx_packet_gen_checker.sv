// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_tx_packet_gen_checker (
    input logic        clk_i,
    input logic        rst_n_i,
    input logic        faw_boundary_i,
    input logic        crc_boundary_i,
    input logic [63:0] s_axis_tdata_i,
    input logic        s_axis_tvalid_i,
    input logic        s_axis_tready_o,
    input logic [63:0] m_axis_tdata_o,
    input logic        m_axis_tdata_isfaw_o,
    input logic        tx_off_i,
    input logic        tx_idle_i,
    input logic        tx_active_i,
    input logic        rx_rdy_i,
    input logic [15:0] crc01_calc,
    input logic [15:0] crc23_calc,
    input logic [15:0] crc45_calc,
    input logic [ 7:0] crcvw_calc,
    input logic        crc_valid
);

   import qeciphy_pkg::*;

   localparam PIPELINE_DEPTH = 3;

   // Calculate past offsets for valid bit checks
   localparam int PAST_V5 = PIPELINE_DEPTH + 1;
   localparam int PAST_V4 = PIPELINE_DEPTH + 2;
   localparam int PAST_V3 = PIPELINE_DEPTH + 3;
   localparam int PAST_V2 = PIPELINE_DEPTH + 4;
   localparam int PAST_V1 = PIPELINE_DEPTH + 5;
   localparam int PAST_V0 = PIPELINE_DEPTH + 6;

   qeciphy_vd_pkt_t vd_pkt;

   assign vd_pkt = qeciphy_vd_pkt_t'(m_axis_tdata_o);  // Only valid PIPELINE_DEPTH cycles after crc_boundary_i

   // Ensure that s_axis_tready_o is reachable
   cover_s_axis_tready_o_C :
   cover property (@(posedge clk_i) s_axis_tready_o);

   // Ensure that non-zero data is transmitted at some point
   cover_non_zero_data_C :
   cover property (@(posedge clk_i) m_axis_tdata_o != 64'd0);

   // Once tx_off_i is asserted, no data should be transmitted after PIPELINE_DEPTH cycles
   property p_tx_off_implies_no_data;
      @(posedge clk_i) disable iff (!rst_n_i) tx_off_i |-> ##PIPELINE_DEPTH(m_axis_tdata_o == IDLE_WORD);
   endproperty

   p_tx_off_implies_no_data_A :
   assert property (p_tx_off_implies_no_data)
   else $error("Data transmitted while transmitter is off");

   // When tx_idle_i is asserted, only boundary characters should be transmitted after PIPELINE_DEPTH cycles
   property p_tx_idle_implies_only_boundary_chars;
      @(posedge clk_i) disable iff (!rst_n_i) m_axis_tdata_o != IDLE_WORD && $past(
          tx_idle_i, PIPELINE_DEPTH
      ) |-> $past(
          faw_boundary_i, PIPELINE_DEPTH
      ) || $past(
          crc_boundary_i, PIPELINE_DEPTH
      );
   endproperty

   p_tx_idle_implies_only_boundary_chars_A :
   assert property (p_tx_idle_implies_only_boundary_chars)
   else $error("Non-boundary characters transmitted while transmitter is idle");

   // Correct valid bits should be transmitted on CRC boundary
   property p_correct_valid_bits_on_crc_boundary;
      bit off_idle;
      @(posedge clk_i) disable iff (!rst_n_i) (crc_boundary_i,
      off_idle = (tx_off_i || tx_idle_i)
      ) |-> ##PIPELINE_DEPTH(off_idle ? (vd_pkt.valids == 6'h0) : ((vd_pkt.valids[5] == $past(
          s_axis_tvalid_i, PAST_V5
      )) && (vd_pkt.valids[4] == $past(
          s_axis_tvalid_i, PAST_V4
      )) && (vd_pkt.valids[3] == $past(
          s_axis_tvalid_i, PAST_V3
      )) && (vd_pkt.valids[2] == $past(
          s_axis_tvalid_i, PAST_V2
      )) && (vd_pkt.valids[1] == $past(
          s_axis_tvalid_i, PAST_V1
      )) && (vd_pkt.valids[0] == $past(
          s_axis_tvalid_i, PAST_V0
      ))));
   endproperty

   p_correct_valid_bits_on_crc_boundary_A :
   assert property (p_correct_valid_bits_on_crc_boundary)
   else $error("Incorrect valid bits transmitted on CRC boundary");

   // FAW pattern should be inserted on FAW boundary
   property p_faw_boundary_inserts_faw_pattern;
      @(posedge clk_i) disable iff (!rst_n_i) faw_boundary_i && !tx_off_i |-> ##PIPELINE_DEPTH(is_faw(
          m_axis_tdata_o
      ));
   endproperty

   p_faw_boundary_inserts_faw_pattern_A :
   assert property (p_faw_boundary_inserts_faw_pattern)
   else $error("FAW boundary did not insert correct FAW pattern");

   // Data presented on s_axis_tdata_i at the time of valid and ready handshake
   // should appear on m_axis_tdata_o after PIPELINE_DEPTH cycles
   property p_tdata_latency;
      logic [63:0] expected_data;
      @(posedge clk_i) disable iff (!rst_n_i) (s_axis_tready_o && s_axis_tvalid_i,
      expected_data = s_axis_tdata_i
      ) |-> ##PIPELINE_DEPTH(m_axis_tdata_o == expected_data);
   endproperty

   p_tdata_latency_A :
   assert property (p_tdata_latency)
   else $error("Data latency from s_axis_tdata_i to m_axis_tdata_o is incorrect");

   // Correct CRC values should be transmitted on CRC boundary
   // crc_valid, crc01_calc, crc23_calc, crc45_calc, crcvw_calc are all from qeciphy_crc_compute module
   property p_correct_crc_packet;
      @(posedge clk_i) disable iff (!rst_n_i) crc_boundary_i && !tx_off_i |-> ##PIPELINE_DEPTH $past(
          crc_valid, 1
      ) && (vd_pkt.crc45 == $past(
          crc45_calc, 1
      )) && (vd_pkt.crc23 == $past(
          crc23_calc, 1
      )) && (vd_pkt.crc01 == $past(
          crc01_calc, 1
      )) && (vd_pkt.crcvw == $past(
          crcvw_calc, 1
      ));
   endproperty

   p_correct_crc_packet_A :
   assert property (p_correct_crc_packet)
   else $error("Incorrect CRC values transmitted on CRC boundary");

   // s_axis_tready_o should only be asserted when tx_active_i is high and not on boundaries
   property p_tready_only_when_active_no_boundaries;
      @(posedge clk_i) disable iff (!rst_n_i) s_axis_tready_o |-> tx_active_i && !faw_boundary_i && !crc_boundary_i;
   endproperty

   p_tready_only_when_active_no_boundaries_A :
   assert property (p_tready_only_when_active_no_boundaries)
   else $error("s_axis_tready_o asserted when transmitter is not active or on boundaries");

   // s_axis_tready_o should be asserted whenever tx_active_i is high and not on boundaries
   property p_tready_asserted_when_active_no_boundaries;
      @(posedge clk_i) disable iff (!rst_n_i) tx_active_i && !faw_boundary_i && !crc_boundary_i |-> s_axis_tready_o;
   endproperty

   p_tready_asserted_when_active_no_boundaries_A :
   assert property (p_tready_asserted_when_active_no_boundaries)
   else $error("s_axis_tready_o not asserted when transmitter is active and not on boundaries");

endmodule
