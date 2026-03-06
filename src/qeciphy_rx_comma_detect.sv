// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Gargi Sunil

module qeciphy_rx_comma_detect #(
    parameter integer TX_PATTERN_LENGTH = 128,
    parameter integer MAX_REVIEWS = 128,
    parameter integer MAX_RETRIES = 32
) (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic        comma_realign_i,
    input  logic [31:0] tdata_i,
    output logic        align_done_o,
    output logic        rx_datapath_resetn_o
);

   // -------------------------------------------------------------
   // Local parameters and type definition
   // -------------------------------------------------------------

   typedef enum logic [5:0] {
      IDLE   = 6'b000001,
      CHECK  = 6'b000010,
      REVIEW = 6'b000100,
      DONE   = 6'b001000,
      FAIL   = 6'b010000,
      RESET  = 6'b100000
   } fsm_t;

   // Comma character mask
   localparam REVIEW_COUNTER_WIDTH = $clog2(MAX_REVIEWS) + 1;
   localparam RX_ALIGN_COUNTER_WIDTH = $clog2(TX_PATTERN_LENGTH);
   localparam RETRIES_COUNTER_WIDTH = $clog2(MAX_RETRIES);
   localparam logic [15:0] FAW1_MSB = 16'h0000;
   localparam logic [15:0] FAW1_LSB = 16'h00BC;
   localparam logic [14:0] FAW2_MSB = 15'h0000;
   localparam logic [15:0] FAW2_LSB = 16'h00CB;
   localparam logic [15:0] CRC1_MSB = 16'h6A0A;
   localparam logic [15:0] CRC1_LSB = 16'h0000;
   localparam logic [15:0] CRC2_MSB = 16'h6A0A;
   localparam logic [15:0] CRC2_LSB = 16'h6A0A;

   // -------------------------------------------------------------
   // Declaration
   // -------------------------------------------------------------
   fsm_t                              fsm_q;
   fsm_t                              fsm_d;
   logic                              fsm_check;
   logic                              fsm_review;
   logic                              fsm_done;
   logic                              fsm_fail;
   logic                              fsm_reset;

   logic [  REVIEW_COUNTER_WIDTH-1:0] rx_align_matched_count_q;
   logic [  REVIEW_COUNTER_WIDTH-1:0] rx_align_matched_count_d;
   logic                              rx_align_matched_count_max_d;
   logic                              rx_align_matched_count_max_q;
   logic [RX_ALIGN_COUNTER_WIDTH-1:0] rx_boundary_count_q;
   logic [RX_ALIGN_COUNTER_WIDTH-1:0] rx_boundary_count_d;
   logic                              rx_align_boundary;
   logic                              rx_align_check_fail_d;
   logic                              rx_align_check_fail_q;
   logic [                      31:0] rx_data;
   logic                              comma_realign;
   logic [ RETRIES_COUNTER_WIDTH-1:0] retries_count_q;
   logic [ RETRIES_COUNTER_WIDTH-1:0] retries_count_d;
   logic                              retries_count_max_d;
   logic                              retries_count_max_q;

   logic [                      15:0] data_msb16;
   logic [                      15:0] data_lsb16;

   logic                              is_faw_1_msb;
   logic                              is_faw_1_lsb;
   logic                              is_faw_2_msb;
   logic                              is_faw_2_lsb;
   logic                              is_crc_1_msb;
   logic                              is_crc_1_lsb;
   logic                              is_crc_2_msb;
   logic                              is_crc_2_lsb;
   logic                              is_data_zero_msb;
   logic                              is_data_zero_lsb;
   logic                              is_faw1;
   logic                              is_faw2;
   logic                              is_crc1;
   logic                              is_crc2;
   logic                              is_data_zero;

   logic                              data_crc_slot_en_d;
   logic                              data_crc_slot_en_q;
   logic                              faw_1_slot_d;
   logic                              faw_1_slot_q;
   logic                              faw_2_slot_d;
   logic                              faw_2_slot_q;
   logic                              data_slot_d;
   logic                              data_slot_q;
   logic                              crc1_slot_d;
   logic                              crc1_slot_q;
   logic                              crc2_slot_d;
   logic                              crc2_slot_q;

   logic [                       3:0] data_crc_slot_count_d;
   logic [                       3:0] data_crc_slot_count_q;


   logic [                       7:0] reset_delay_count_q;
   logic [                       7:0] reset_delay_count_d;
   logic                              reset_delay_done_d;
   logic                              reset_delay_done_q;

   // -------------------------------------------------------------
   // FAW/CRC/Data Detection
   // -------------------------------------------------------------

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         rx_data <= '0;
      end else begin
         rx_data <= tdata_i;
      end
   end

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         comma_realign <= '0;
      end else begin
         comma_realign <= comma_realign_i;
      end
   end

   assign data_msb16 = rx_data[31:16];
   assign data_lsb16 = rx_data[15:0];

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         is_faw_1_msb     <= '0;
         is_faw_1_lsb     <= '0;
         is_faw_2_msb     <= '0;
         is_faw_2_lsb     <= '0;
         is_crc_1_msb     <= '0;
         is_crc_1_lsb     <= '0;
         is_crc_2_msb     <= '0;
         is_crc_2_lsb     <= '0;
         is_data_zero_msb <= '0;
         is_data_zero_lsb <= '0;
      end else begin
         is_faw_1_msb     <= (data_msb16 == FAW1_MSB);
         is_faw_1_lsb     <= (data_lsb16 == FAW1_LSB);
         is_faw_2_msb     <= (data_msb16[14:0] == FAW2_MSB);
         is_faw_2_lsb     <= (data_lsb16 == FAW2_LSB);
         is_crc_1_msb     <= (data_msb16 == CRC1_MSB);
         is_crc_1_lsb     <= (data_lsb16 == CRC1_LSB);
         is_crc_2_msb     <= (data_msb16 == CRC2_MSB);
         is_crc_2_lsb     <= (data_lsb16 == CRC2_LSB);
         is_data_zero_msb <= (data_msb16 == 16'h0000);
         is_data_zero_lsb <= (data_lsb16 == 16'h0000);
      end
   end

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         is_faw1 <= '0;
         is_faw2 <= '0;
         is_crc1 <= '0;
         is_crc2 <= '0;
         is_data_zero <= '0;
      end else begin
         is_faw1 <= is_faw_1_msb & is_faw_1_lsb;
         is_faw2 <= is_faw_2_msb & is_faw_2_lsb;
         is_crc1 <= is_crc_1_msb & is_crc_1_lsb;
         is_crc2 <= is_crc_2_msb & is_crc_2_lsb;
         is_data_zero <= is_data_zero_msb & is_data_zero_lsb;
      end
   end

   // -------------------------------------------------------------
   // FSM states
   // -------------------------------------------------------------

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         fsm_q <= IDLE;
      end else begin
         fsm_q <= fsm_d;
      end
   end

   always_comb begin
      case (fsm_q)
         IDLE:    fsm_d = CHECK;
         CHECK:   fsm_d = is_faw1 ? REVIEW : CHECK;
         REVIEW:  fsm_d = (comma_realign || rx_align_check_fail_q) ? FAIL : (rx_align_matched_count_max_q ? DONE : REVIEW);
         DONE:    fsm_d = DONE;
         FAIL:    fsm_d = retries_count_max_q ? RESET : IDLE;
         RESET:   fsm_d = reset_delay_done_q ? IDLE : RESET;
         default: fsm_d = IDLE;
      endcase
   end

   assign fsm_check = fsm_q[1];
   assign fsm_review = fsm_q[2];
   assign fsm_done = fsm_q[3];
   assign fsm_fail = fsm_q[4];
   assign fsm_reset = fsm_q[5];

   // -------------------------------------------------------------
   // Review : Boundary check and alignment matched counters
   // -------------------------------------------------------------

   // Boundary counter
   assign rx_boundary_count_d = fsm_review ? rx_boundary_count_q + RX_ALIGN_COUNTER_WIDTH'(1'b1) : '0;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         rx_boundary_count_q <= '0;
      end else begin
         rx_boundary_count_q <= rx_boundary_count_d;
      end
   end

   // Valid slot generation for FAWs, DATA and CRC
   assign data_crc_slot_en_d = is_faw1 && fsm_check ? 1'b1 :
                               !fsm_review ? 1'b0 :
                               rx_boundary_count_q == RX_ALIGN_COUNTER_WIDTH'(TX_PATTERN_LENGTH-3) ? 1'b0 : 
                               rx_boundary_count_q == RX_ALIGN_COUNTER_WIDTH'(TX_PATTERN_LENGTH-1) ? 1'b1:
                               data_crc_slot_en_q;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         data_crc_slot_en_q <= 1'b0;
      end else begin
         data_crc_slot_en_q <= data_crc_slot_en_d;
      end
   end

   assign data_crc_slot_count_d = data_crc_slot_en_q ? ((data_crc_slot_count_q == 4'd13) ? '0 : data_crc_slot_count_q + 4'd1) : '0;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         data_crc_slot_count_q <= '0;
      end else begin
         data_crc_slot_count_q <= data_crc_slot_count_d;
      end
   end

   assign data_slot_d = !data_crc_slot_en_q ? 1'b0 : data_crc_slot_count_q == 4'd12 ? 1'b0 : data_crc_slot_count_q == 4'd0 ? 1'b1 : data_slot_q;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         data_slot_q <= '0;
      end else begin
         data_slot_q <= data_slot_d;
      end
   end

   assign crc1_slot_d = data_crc_slot_count_q == 4'd12;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc1_slot_q <= '0;
      end else begin
         crc1_slot_q <= crc1_slot_d;
      end
   end

   assign crc2_slot_d = data_crc_slot_count_q == 4'd13;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc2_slot_q <= '0;
      end else begin
         crc2_slot_q <= crc2_slot_d;
      end
   end

   assign faw_1_slot_d = rx_boundary_count_q == RX_ALIGN_COUNTER_WIDTH'(TX_PATTERN_LENGTH - 2);

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_1_slot_q <= '0;
      end else begin
         faw_1_slot_q <= faw_1_slot_d;
      end
   end

   assign faw_2_slot_d = (is_faw1 && fsm_check) || (rx_boundary_count_q == RX_ALIGN_COUNTER_WIDTH'(TX_PATTERN_LENGTH - 1));

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_2_slot_q <= '0;
      end else begin
         faw_2_slot_q <= faw_2_slot_d;
      end
   end

   assign rx_align_boundary = (rx_boundary_count_q == RX_ALIGN_COUNTER_WIDTH'(TX_PATTERN_LENGTH - 1));

   assign rx_align_check_fail_d = fsm_review & ((data_slot_q ^ is_data_zero) | (crc1_slot_q ^ is_crc1) | (crc2_slot_q ^ is_crc2) | (faw_1_slot_q ^ is_faw1) | (faw_2_slot_q ^ is_faw2));

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         rx_align_check_fail_q <= '0;
      end else begin
         rx_align_check_fail_q <= rx_align_check_fail_d;
      end
   end

   assign rx_align_matched_count_d = fsm_review ? (rx_align_boundary ? rx_align_matched_count_q + REVIEW_COUNTER_WIDTH'(1'b1) : rx_align_matched_count_q) : '0;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         rx_align_matched_count_q <= '0;
      end else begin
         rx_align_matched_count_q <= rx_align_matched_count_d;
      end
   end

   assign rx_align_matched_count_max_d = (rx_align_matched_count_q == REVIEW_COUNTER_WIDTH'(MAX_REVIEWS));

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         rx_align_matched_count_max_q <= '0;
      end else begin
         rx_align_matched_count_max_q <= rx_align_matched_count_max_d;
      end
   end

   // -------------------------------------------------------------
   // Retries Counter
   // -------------------------------------------------------------

   assign retries_count_d = fsm_reset ? '0 : (fsm_fail ? retries_count_q + RETRIES_COUNTER_WIDTH'(1'b1) : retries_count_q);
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         retries_count_q <= '0;
      end else begin
         retries_count_q <= retries_count_d;
      end
   end

   assign retries_count_max_d = retries_count_q == RETRIES_COUNTER_WIDTH'(MAX_RETRIES - 1);
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         retries_count_max_q <= '0;
      end else begin
         retries_count_max_q <= retries_count_max_d;
      end
   end

   // -------------------------------------------------------------
   // Reset Delay Counter
   // -------------------------------------------------------------

   assign reset_delay_count_d = !fsm_reset ? 8'd0 : (reset_delay_count_q == 8'd255) ? reset_delay_count_q : reset_delay_count_q + 8'd1;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         reset_delay_count_q <= 8'd0;
      end else begin
         reset_delay_count_q <= reset_delay_count_d;
      end
   end

   assign reset_delay_done_d = (reset_delay_count_q == 8'd255);

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         reset_delay_done_q <= 1'b0;
      end else begin
         reset_delay_done_q <= reset_delay_done_d;
      end
   end

   // -------------------------------------------------------------
   // Output assignments
   // -------------------------------------------------------------

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         align_done_o <= 1'b0;
      end else begin
         align_done_o <= fsm_done;
      end
   end

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         rx_datapath_resetn_o <= 1'b1;
      end else begin
         rx_datapath_resetn_o <= ~fsm_reset;
      end
   end

endmodule  // qeciphy_rx_comma_detect
