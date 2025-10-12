// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: aniketEng, Dogancan Davutoglu

`include "qeciphy_pkg.sv"

module qeciphy_rx_channeldecoder (
    input  logic        gt_rx_clk,
    input  logic        rx_clk,
    input  logic        rst_n,
    input  logic [31:0] i_gt_rx_data,
    output logic [63:0] o_rx_data,
    output logic        o_rx_valid,
    output logic        o_rx_rdy,
    output logic        o_remote_rx_rdy,
    output logic        o_remote_pd_req,
    output logic        o_remote_pd_ack,
    output logic        o_fap_missing,
    output logic        o_crc_mismatch
);

   import qeciphy_pkg::*;

   // -------------------------------------------------------------
   // Local declaration
   // -------------------------------------------------------------

   logic [63:0] rx_data_opt[0:3];
   logic [31:0] rx_data_reg[0:3];
   logic [31:0] gt_rx_data_q;
   logic [63:0] rx_data;
   logic ptr;
   logic [1:0] option;
   logic [1:0] option_nxt;

   logic [8:0] fa_counter;
   logic [8:0] fa_counter_nxt;
   logic fa_counter_done;

   logic [2:0] crc_counter;
   logic crc_counter_done;

   logic [15:0] crc01;
   logic [15:0] crc23;
   logic [15:0] crc45;
   logic [7:0] crcvw;

   logic crc_cnt_rst;
   logic crc_inst_rst_n;
   logic [2:0] crc_counter_nxt;
   logic [5:0] crc_en_sr;
   logic [5:0] crc_en_sr_nxt;
   logic crc01_en;
   logic crc23_en;
   logic crc45_en;
   logic crcvw_en;

   logic crc01_match;
   logic crc23_match;
   logic crc45_match;
   logic crcvw_match;

   logic [63:0] o_data_sr[0:6];
   logic [5:0] o_valid_sr;
   logic [5:0] o_valid_sr_nxt;
   logic [7:0] valid_field;

   logic state_word_align;
   logic state_ready;

   logic crc_boundary_check;
   logic fa_boundary_check;

   // -------------------------------------------------------------
   // Type definition
   // -------------------------------------------------------------

   typedef enum bit [2:0] {
      RESET,
      SEARCH_FA,
      WORD_ALIGN,
      FIRST_CYCLE,
      READY,
      ERROR
   } fsm_t;

   fsm_t state, state_nxt;

   localparam REMOTE_RX_RDY_BIT = 63;
   localparam REMOTE_PD_REQ_BIT = 62;
   localparam REMOTE_PD_ACK_BIT = 61;

   // -------------------------------------------------------------
   // Convert the 32-bit words captured on gt_rx_clk to 64-bit words on rx_clk
   // -------------------------------------------------------------

   always_ff @(posedge gt_rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         gt_rx_data_q <= '0;
      end else begin
         gt_rx_data_q <= i_gt_rx_data;
      end
   end

   always_ff @(posedge gt_rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         rx_data_reg[0] <= 32'd0;
         rx_data_reg[1] <= 32'd0;
         rx_data_reg[2] <= 32'd0;
         rx_data_reg[3] <= 32'd0;
      end else begin
         rx_data_reg[{1'b0, ptr}] <= i_gt_rx_data;
         rx_data_reg[{1'b1, ptr}] <= gt_rx_data_q;
      end
   end

   always_ff @(posedge gt_rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         ptr <= 1'b0;
      end else begin
         ptr <= ~ptr;
      end
   end

   always_ff @(posedge rx_clk) begin
      rx_data_opt[0] <= {rx_data_reg[0], rx_data_reg[1]};
      rx_data_opt[1] <= {rx_data_reg[1], rx_data_reg[0]};
      rx_data_opt[2] <= {rx_data_reg[2], rx_data_reg[3]};
      rx_data_opt[3] <= {rx_data_reg[3], rx_data_reg[2]};
   end

   assign rx_data = rx_data_opt[option];

   // -------------------------------------------------------------
   // FSM
   // -------------------------------------------------------------

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) state <= RESET;
      else state <= state_nxt;
   end

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) option <= '0;
      else option <= option_nxt;
   end

   assign option_nxt = (state == SEARCH_FA) & is_faw(rx_data_opt[1]) ? 2'h1 : (state == SEARCH_FA) & is_faw(rx_data_opt[2]) ? 2'h2 : (state == SEARCH_FA) & is_faw(rx_data_opt[3]) ? 2'h3 : option;

   always_comb begin
      case (state)
         RESET:       state_nxt = SEARCH_FA;
         SEARCH_FA:   state_nxt = is_faw(rx_data_opt[0]) | is_faw(rx_data_opt[1]) | is_faw(rx_data_opt[2]) | is_faw(rx_data_opt[3]) ? WORD_ALIGN : SEARCH_FA;
         WORD_ALIGN:  state_nxt = FIRST_CYCLE;
         FIRST_CYCLE: state_nxt = is_faw(rx_data_opt[option]) ? READY : FIRST_CYCLE;
         READY:       state_nxt = o_fap_missing | o_crc_mismatch ? ERROR : READY;
         ERROR:       state_nxt = ERROR;
         default:     state_nxt = fsm_t'(1'bx);
      endcase
   end

   assign state_word_align = (state == WORD_ALIGN);
   assign state_ready = (state == READY);

   // -------------------------------------------------------------
   // Counters
   // -------------------------------------------------------------

   // Once the FAW is detected by the state machine, the FSM transitions to WORD_ALIGN in the following cycle, 
   // and in the cycle after that, we set fa_counter. Therefore, we initialize fa_counter to two.  
   assign fa_counter_nxt = state_word_align ? 9'h2 : fa_counter + 9'h1;

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         fa_counter <= '0;
      end else begin
         fa_counter <= fa_counter_nxt;
      end
   end

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         fa_counter_done <= 1'b0;
      end else begin
         fa_counter_done <= (fa_counter == '1);
      end
   end

   assign crc_cnt_rst = fa_counter_done || crc_counter_done;
   assign crc_counter_nxt = state_word_align ? 3'd1 : crc_cnt_rst ? 3'h0 : crc_counter + 3'h1;

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         crc_counter <= 3'd1;
      end else begin
         crc_counter <= crc_counter_nxt;
      end
   end

   always_ff @(posedge rx_clk) begin
      crc_counter_done <= (crc_counter == 3'h5);
      // This should be asserted after every six Data Words.
   end

   assign fa_boundary_check = state_ready && fa_counter_done;
   assign crc_boundary_check = state_ready && crc_counter_done;

   // -------------------------------------------------------------
   // Compute and match CRC
   // -------------------------------------------------------------

   // We have four CRC modules:
   // crc01, crc23 and crc45 blocks are responsible for computing CRC16 on two consecutive data words.
   // crcvw block is responsible for computing CRC8 of the validation field.
   //                ___     ___     ___     ___     ___     ___     ___     ___
   // rx_clk    ____|   |___|   |___|   |___|   |___|   |___|   |___|   |___|   |___
   //
   //                _______________     
   // crc01_en  ____|               |_______________________________________________
   //             
   //                                _______________     
   // crc23_en  ____________________|               |_______________________________
   //             
   //                                                _______________     
   // crc45_en  ____________________________________|               |_______________
   //
   //                                                                _______
   // crcvw_en  ____________________________________________________|       |_______

   assign crc01_match = crc01 == rx_data[31:16];
   assign crc23_match = crc23 == rx_data[47:32];
   assign crc45_match = crc45 == rx_data[63:48];

   assign crc01_en = crc_en_sr[1];
   assign crc23_en = crc_en_sr[3];
   assign crc45_en = crc_en_sr[5];

   assign crcvw_en = crc_counter_done;
   assign crcvw_match = crcvw == rx_data[7:0];
   assign valid_field = {rx_data[15:8]};

   assign crc_en_sr_nxt = crc_cnt_rst ? 6'h3 : (crc_en_sr << 1);

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) crc_en_sr <= '0;
      else crc_en_sr <= crc_en_sr_nxt;
   end

   assign crc_inst_rst_n = ~crc_cnt_rst && rst_n;

   qeciphy_crc16_ibm3740 i_crc_data01 (
       .clk    (rx_clk),
       .rst_n  (crc_inst_rst_n),
       .i_data (rx_data),
       .i_valid(crc01_en),
       .o_crc  (crc01)
   );

   qeciphy_crc16_ibm3740 i_crc_data23 (
       .clk    (rx_clk),
       .rst_n  (crc_inst_rst_n),
       .i_data (rx_data),
       .i_valid(crc23_en),
       .o_crc  (crc23)
   );

   qeciphy_crc16_ibm3740 i_crc_data45 (
       .clk    (rx_clk),
       .rst_n  (crc_inst_rst_n),
       .i_data (rx_data),
       .i_valid(crc45_en),
       .o_crc  (crc45)
   );

   qeciphy_crc8_smbus i_crc_vw (
       .data_i (valid_field),
       .valid_i(crcvw_en),
       .crc_o  (crcvw)
   );

   // -------------------------------------------------------------
   // Output data pipeline
   // -------------------------------------------------------------

   // Hold the output until the validation word is received
   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         for (int i = 0; i < 7; i++) begin
            o_data_sr[i] <= '0;
         end
      end else if (state_ready) begin
         o_data_sr[6] <= rx_data;
         for (int i = 1; i < 7; i++) begin
            o_data_sr[i-1] <= o_data_sr[i];
         end
      end
   end

   // -------------------------------------------------------------
   // Determine valid output packets based on Validation Word
   // -------------------------------------------------------------

   assign o_valid_sr_nxt = crc_boundary_check ? {rx_data[13:8]} : {1'b0, o_valid_sr[5:1]};

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         o_valid_sr <= '0;
      end else begin
         o_valid_sr <= o_valid_sr_nxt;
      end
   end

   // -------------------------------------------------------------
   // Outputs
   // -------------------------------------------------------------

   assign o_rx_data  = o_data_sr[0];
   assign o_rx_valid = o_valid_sr[0] & state_ready;
   assign o_rx_rdy   = state_ready;

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         o_remote_rx_rdy <= 1'b0;
      end else if (fa_boundary_check) begin  // Monitor this even if state != READY
         o_remote_rx_rdy <= rx_data[REMOTE_RX_RDY_BIT];
      end
   end

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         o_remote_pd_req <= 1'b0;
      end else if (fa_boundary_check) begin
         o_remote_pd_req <= rx_data[REMOTE_PD_REQ_BIT];
      end
   end

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         o_remote_pd_ack <= 1'b0;
      end else if (fa_boundary_check) begin
         o_remote_pd_ack <= rx_data[REMOTE_PD_ACK_BIT];
      end
   end

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         o_fap_missing <= 1'b0;
      end else if (fa_boundary_check) begin
         o_fap_missing <= ~is_faw(rx_data);
      end
   end

   always_ff @(posedge rx_clk or negedge rst_n) begin
      if (~rst_n) begin
         o_crc_mismatch <= 1'b0;
      end else if (crc_boundary_check) begin
         o_crc_mismatch <= ~(crc01_match && crc23_match && crc45_match && crcvw_match);
      end
   end

endmodule  // qeciphy_rx_channeldecoder
