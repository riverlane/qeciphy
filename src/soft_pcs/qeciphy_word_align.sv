// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Dogancan Davutoglu (integration)
//
// Word aligner with automatic comma-based alignment.
//
//
// DATA_WIDTH must equal 4 * WORD_SIZE (e.g. 40 = 4 * 10).

module qeciphy_word_align #(
    parameter                 DATA_WIDTH         = 40,
    parameter                 WORD_SIZE          = 10,
    parameter                 TX_PATTERN_LENGTH  = 128,
    parameter                 RXSLIDE_COUNT_MAX  = 80,
    parameter                 RX_ALIGN_MATCH_MAX = 8,
    parameter [WORD_SIZE-1:0] COMMA_POS          = 10'b0101111100,
    parameter [WORD_SIZE-1:0] COMMA_NEG          = 10'b1010000011
) (
    input  logic                      clk,
    input  logic                      rst_n_i,
    input  logic [DATA_WIDTH - 1 : 0] rx_datain,
    output logic [DATA_WIDTH - 1 : 0] rx_dataout,
    output logic                      o_align_done,
    output logic                      o_align_fail
);

   // ----------------------------------------------------------------
   // Barrel-shifter parameters
   // ----------------------------------------------------------------
   localparam BUFFER_SIZE = 4 * DATA_WIDTH;

   // synthesis translate_off
   initial begin
      if (DATA_WIDTH != 4 * WORD_SIZE) begin
         $display("Not tested for parameters where DATA_WIDTH != 4 * WORD_SIZE");
         $stop();
      end
   end
   // synthesis translate_on

   // ----------------------------------------------------------------
   // Alignment FSM parameters (from qeciphy_rx_bytealigner)
   // ----------------------------------------------------------------
   localparam RXSLIDE_COUNT_WIDTH = $clog2(RXSLIDE_COUNT_MAX);
   localparam PATTERN_COUNT_WIDTH = $clog2(TX_PATTERN_LENGTH);

   typedef enum logic [2:0] {
      IDLE   = 3'h0,
      SLIDE  = 3'h1,
      CHECK  = 3'h2,
      REVIEW = 3'h3,
      DONE   = 3'h4,
      FAIL   = 3'h5
   } fsm_t;

   // ----------------------------------------------------------------
   // Signal declarations
   // ----------------------------------------------------------------

   // Barrel shifter
   logic [              5 : 0] position;
   logic [BUFFER_SIZE - 1 : 0] buffer;

   // Internal slide (driven by FSM)
   logic                       do_slide;

   // FSM
   fsm_t                       fsm;
   fsm_t                       fsm_nxt;
   logic                       fsm_idle;
   logic                       fsm_slide;
   logic                       fsm_check;
   logic                       fsm_review;
   logic                       fsm_done;
   logic                       fsm_fail;

   // Comma detection on encoded output
   localparam NUM_SYMBOLS = DATA_WIDTH / WORD_SIZE;
   logic [       DATA_WIDTH-1:0] rx_data_q;
   logic                         rx_datan_comma_m;

   // Counters
   logic [RXSLIDE_COUNT_WIDTH:0] rx_slide_count;
   logic [RXSLIDE_COUNT_WIDTH:0] rx_slide_count_nxt;
   logic                         rx_slide_count_max;

   logic [PATTERN_COUNT_WIDTH:0] rx_pattern_count;
   logic [PATTERN_COUNT_WIDTH:0] rx_pattern_count_nxt;
   logic                         rx_pattern_count_max;

   logic [                  3:0] rx_align_matched_count;
   logic [                  3:0] rx_align_matched_count_nxt;
   logic                         rx_align_matched_count_max;

   logic [                  9:0] rx_align_timeout_count;
   logic [                  9:0] rx_align_timeout_count_nxt;
   logic                         rx_align_boundary_check;
   logic                         rx_align_boundary_check_fail;
   logic                         rx_align_matched;

   // ================================================================
   // Barrel shifter 
   // ================================================================

   always_ff @(posedge clk or negedge rst_n_i) begin
      if (!rst_n_i) begin
         position   <= '0;
         rx_dataout <= '0;
         buffer     <= '0;
      end else begin
         buffer     <= {rx_datain, buffer[BUFFER_SIZE-1 : DATA_WIDTH]};
         rx_dataout <= buffer[BUFFER_SIZE-1-DATA_WIDTH-position-:DATA_WIDTH];

         if (do_slide) begin
            position <= (position == (DATA_WIDTH - 1)) ? 6'd0 : position + 6'd1;
         end
      end
   end

   // ================================================================
   // Comma detection in encoded domain
   // ================================================================
   // Search for K28.5 (positive or negative disparity) at any WORD_SIZE
   // boundary in the barrel-shifter output.

   always_ff @(posedge clk) begin
      if (!rst_n_i) rx_data_q <= '0;
      else rx_data_q <= rx_dataout;
   end

   always_comb begin
      rx_datan_comma_m = 1'b0;
      if (rx_data_q[WORD_SIZE:0] == COMMA_POS || rx_data_q[WORD_SIZE:0] == COMMA_NEG) rx_datan_comma_m = 1'b1;
   end

   // ================================================================
   // Alignment FSM
   // ================================================================

   always_ff @(posedge clk) begin
      if (!rst_n_i) fsm <= IDLE;
      else fsm <= fsm_nxt;
   end

   always_comb begin
      case (fsm)
         IDLE:    fsm_nxt = SLIDE;
         SLIDE:   fsm_nxt = CHECK;
         CHECK:   fsm_nxt = rx_datan_comma_m ? REVIEW : rx_pattern_count_max ? (rx_slide_count_max ? FAIL : SLIDE) : CHECK;
         REVIEW:  fsm_nxt = rx_align_matched_count_max ? DONE : rx_align_boundary_check_fail ? FAIL : REVIEW;
         DONE:    fsm_nxt = DONE;
         FAIL:    fsm_nxt = IDLE;
         default: fsm_nxt = IDLE;
      endcase
   end

   assign fsm_idle = (fsm == IDLE);
   assign fsm_slide = (fsm == SLIDE);
   assign fsm_check = (fsm == CHECK);
   assign fsm_review = (fsm == REVIEW);
   assign fsm_done = (fsm == DONE);
   assign fsm_fail = (fsm == FAIL);

   // Internal slide: assert for one cycle in SLIDE state
   assign do_slide = fsm_slide;

   // ================================================================
   // Counters (from qeciphy_rx_bytealigner)
   // ================================================================

   assign rx_slide_count_max = (rx_slide_count == RXSLIDE_COUNT_MAX[RXSLIDE_COUNT_WIDTH:0] - 1);
   assign rx_pattern_count_max = (rx_pattern_count == TX_PATTERN_LENGTH[PATTERN_COUNT_WIDTH:0] - 1);

   // Slide counter: how many bit positions we have tried
   always_ff @(posedge clk) begin
      if (!rst_n_i) rx_slide_count <= '0;
      else rx_slide_count <= rx_slide_count_nxt;
   end

   assign rx_slide_count_nxt = fsm_idle                                              ? '0 :
                                fsm_check & rx_pattern_count_max & rx_slide_count_max ? '0 :
                                fsm_check & rx_pattern_count_max                      ? rx_slide_count + 1 :
                                fsm_check & rx_datan_comma_m                          ? '0 :
                                                                                        rx_slide_count;

   // Pattern counter: cycles since last slide (wait for data to propagate)
   always_ff @(posedge clk) begin
      if (!rst_n_i) rx_pattern_count <= '0;
      else rx_pattern_count <= rx_pattern_count_nxt;
   end

   assign rx_pattern_count_nxt = fsm_idle ? '0 : fsm_check & rx_pattern_count_max ? '0 : fsm_check & rx_datan_comma_m ? '0 : fsm_check ? rx_pattern_count + 1 : rx_pattern_count;

   // ================================================================
   // Alignment verification (REVIEW state)
   // ================================================================

   assign rx_align_matched     = fsm_review & rx_datan_comma_m & rx_align_boundary_check;

   always_ff @(posedge clk) begin
      if (!rst_n_i) rx_align_matched_count <= '0;
      else rx_align_matched_count <= rx_align_matched_count_nxt;
   end

   assign rx_align_matched_count_nxt = fsm_review ? (rx_align_matched ? rx_align_matched_count + 1 : rx_align_matched_count) : '0;
   assign rx_align_matched_count_max = (rx_align_matched_count == RX_ALIGN_MATCH_MAX[3:0]);

   // Timeout counter for periodic boundary checks during REVIEW
   always_ff @(posedge clk) begin
      if (!rst_n_i) rx_align_timeout_count <= '0;
      else rx_align_timeout_count <= rx_align_timeout_count_nxt;
   end

   assign rx_align_timeout_count_nxt   = !fsm_review ? 0 : (rx_align_timeout_count == TX_PATTERN_LENGTH[PATTERN_COUNT_WIDTH:0] - 1) ? 0 : rx_align_timeout_count + 1;
   assign rx_align_boundary_check      = (rx_align_timeout_count == TX_PATTERN_LENGTH[PATTERN_COUNT_WIDTH:0] - 1);
   assign rx_align_boundary_check_fail = rx_align_boundary_check ^ rx_datan_comma_m;

   // ================================================================
   // Output assignments
   // ================================================================

   always_ff @(posedge clk) begin
      if (!rst_n_i) begin
         o_align_done <= 1'b0;
         o_align_fail <= 1'b0;
      end else begin
         o_align_done <= fsm_done;
         o_align_fail <= fsm_fail;
      end
   end

endmodule  // qeciphy_word_align
