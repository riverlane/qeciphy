// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta, Dogancan Davutoglu

`include "qeciphy_pkg.sv"

module qeciphy_tx_channelencoder (
    input  logic        gt_tx_clk,
    output logic [31:0] o_gt_tx_data,

    input  logic        tx_clk,
    input  logic        rst_n,
    input  logic [63:0] i_tx_data,
    output logic        o_tx_ready,
    input  logic        i_tx_valid,
    input  logic        i_rx_rdy,
    input  logic        i_remote_rx_rdy,
    input  logic        i_pd_req,
    input  logic        i_pd_ack
);

   import qeciphy_pkg::*;

   // -------------------------------------------------------------
   // Local declaration
   // -------------------------------------------------------------

   logic [8:0] fa_counter;
   logic fa_counter_done;

   logic [2:0] crc_counter;
   logic crc_counter_done;

   logic [7:0] valid_sr;
   logic [63:0] tx_data_nxt;
   logic [63:0] tx_data;

   logic crc_cnt_rst;
   logic crc_inst_rst_n;
   logic [2:0] crc_counter_nxt;
   logic [5:0] crc_en_sr;
   logic [5:0] crc_en_sr_nxt;
   logic crc01_en;
   logic crc23_en;
   logic crc45_en;
   logic crcvw_en;
   logic [15:0] crc01;
   logic [15:0] crc23;
   logic [15:0] crc45;
   logic [7:0] crcvw;

   logic cycle;

   logic pd_req;
   logic pd_ack;

   // -------------------------------------------------------------
   // Transmit 32 bits per cycle using the gt_tx_clk
   // -------------------------------------------------------------

   always_ff @(posedge gt_tx_clk or negedge rst_n) begin
      if (~rst_n) begin
         cycle <= 1'b0;
      end else begin
         cycle <= ~cycle;
      end
   end

   always_ff @(posedge gt_tx_clk) begin
      if (~cycle) begin
         o_gt_tx_data <= tx_data[31:0];
      end else begin
         o_gt_tx_data <= tx_data[63:32];
      end
   end

   // ----------------------------------------------------
   // Counters
   // ----------------------------------------------------

   always_ff @(posedge tx_clk or negedge rst_n) begin
      if (~rst_n) begin
         fa_counter <= '0;
      end else begin
         fa_counter <= fa_counter + 9'd1;
      end
   end

   always_ff @(posedge tx_clk or negedge rst_n) begin
      if (~rst_n) begin
         fa_counter_done <= 1'b0;
      end else begin
         fa_counter_done <= (fa_counter == '1);
      end
   end

   assign crc_cnt_rst = fa_counter_done || crc_counter_done;
   assign crc_counter_nxt = crc_cnt_rst ? 3'h0 : crc_counter + 3'h1;

   always_ff @(posedge tx_clk or negedge rst_n) begin
      if (~rst_n) begin
         crc_counter <= 3'd1;
         // Align the counter correctly
      end else begin
         crc_counter <= crc_counter_nxt;
      end
   end

   always_ff @(posedge tx_clk or negedge rst_n) begin
      if (~rst_n) begin
         crc_counter_done <= 1'b0;
      end else begin
         crc_counter_done <= (crc_counter == 3'h5);
         // This should be asserted after every six Data Words.
      end
   end

   // -------------------------------------------------------------
   // Compute CRC
   // -------------------------------------------------------------

   assign crc01_en = crc_en_sr[1];
   assign crc23_en = crc_en_sr[3];
   assign crc45_en = crc_en_sr[5];
   assign crcvw_en = crc_counter_done;

   assign crc_en_sr_nxt = crc_cnt_rst ? 6'h3 : (crc_en_sr << 1);

   always_ff @(posedge tx_clk or negedge rst_n) begin
      if (~rst_n) crc_en_sr <= '0;
      else crc_en_sr <= crc_en_sr_nxt;
   end

   assign crc_inst_rst_n = ~crc_cnt_rst && rst_n;

   qeciphy_crc16_ibm3740 i_crc_data01 (
       .clk    (tx_clk),
       .rst_n  (crc_inst_rst_n),
       .i_data (tx_data_nxt),
       .i_valid(crc01_en),
       .o_crc  (crc01)
   );

   qeciphy_crc16_ibm3740 i_crc_data23 (
       .clk    (tx_clk),
       .rst_n  (crc_inst_rst_n),
       .i_data (tx_data_nxt),
       .i_valid(crc23_en),
       .o_crc  (crc23)
   );

   qeciphy_crc16_ibm3740 i_crc_data45 (
       .clk    (tx_clk),
       .rst_n  (crc_inst_rst_n),
       .i_data (tx_data_nxt),
       .i_valid(crc45_en),
       .o_crc  (crc45)
   );

   qeciphy_crc8_smbus i_crc_vw (
       .data_i (valid_sr),
       .valid_i(crcvw_en),
       .crc_o  (crcvw)
   );

   // ----------------------------------------------------
   // Pack 64 bits per cycle using the tx_clk
   // ----------------------------------------------------

   assign pd_req = i_pd_req && ~i_tx_valid;
   assign pd_ack = i_pd_ack && ~i_tx_valid;

   always_ff @(posedge tx_clk or negedge rst_n) begin
      if (~rst_n) begin
         valid_sr <= '0;
      end else if (o_tx_ready) begin
         valid_sr <= {2'b00, i_tx_valid, valid_sr[5:1]};
      end
   end

   assign tx_data_nxt =   fa_counter_done ? {i_rx_rdy, pd_req, pd_ack, 21'h0, WORD_ALIGNMENT_COMMA, 24'h0, BYTE_ALIGNMENT_COMMA} :
                          crc_counter_done ? {crc45, crc23, crc01, valid_sr, crcvw} :
                          i_tx_valid && o_tx_ready ? i_tx_data : 64'h0;

   always_ff @(posedge tx_clk or negedge rst_n) begin
      if (~rst_n) begin
         tx_data <= '0;
      end else begin
         tx_data <= tx_data_nxt;
      end
   end

   // ----------------------------------------------------
   // Assign outputs
   // ----------------------------------------------------

   assign o_tx_ready = rst_n && ~crc_cnt_rst && i_remote_rx_rdy;

endmodule  // qeciphy_tx_channelencoder
