// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Evan Sun, Kauser Johar
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
    input  logic                      clk_i,
    input  logic                      rst_n_i,
    input  logic [DATA_WIDTH - 1 : 0] rx_datain_i,
    output logic [DATA_WIDTH - 1 : 0] rx_dataout_o,
    output logic                      align_done_o,
    output logic                      align_fail_o
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
   // Alignment FSM parameters
   // ----------------------------------------------------------------
   localparam RXSLIDE_COUNT_WIDTH = $clog2(RXSLIDE_COUNT_MAX);
   localparam PATTERN_COUNT_WIDTH = $clog2(TX_PATTERN_LENGTH);
   localparam POSITION_WIDTH = $clog2(DATA_WIDTH);

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
   logic [ POSITION_WIDTH - 1 : 0] position;
   logic [    BUFFER_SIZE - 1 : 0] buffer;

   // Internal slide (driven by FSM)
   logic                           do_slide;

   // FSM
   fsm_t                           fsm;
   fsm_t                           fsm_nxt;
   logic                           fsm_idle;
   logic                           fsm_slide;
   logic                           fsm_check;
   logic                           fsm_review;
   logic                           fsm_done;
   logic                           fsm_fail;

   // Registered FSM transition conditions (reduces combinational fan-in)
   logic                           check_to_review_q;  // Comma detected in CHECK
   logic                           check_to_slide_q;  // Pattern timeout, retry slide
   logic                           check_to_fail_q;  // Pattern timeout, no more slides
   logic                           review_to_done_q;  // Enough matches in REVIEW
   logic                           review_to_fail_q;  // Boundary check failed in REVIEW

   // Comma detection on encoded output
   logic [         DATA_WIDTH-1:0] rx_data_q;
   logic                           rx_datan_comma_m_nxt;
   logic                           rx_datan_comma_m;

   // Counters
   logic [RXSLIDE_COUNT_WIDTH-1:0] rx_slide_count;
   logic [RXSLIDE_COUNT_WIDTH-1:0] rx_slide_count_nxt;
   logic                           rx_slide_count_max;

   logic [PATTERN_COUNT_WIDTH-1:0] rx_pattern_count;
   logic [PATTERN_COUNT_WIDTH-1:0] rx_pattern_count_nxt;
   logic                           rx_pattern_count_max;

   logic [                    3:0] rx_align_matched_count;
   logic [                    3:0] rx_align_matched_count_nxt;
   logic                           rx_align_matched_count_max;

   logic [PATTERN_COUNT_WIDTH-1:0] rx_align_timeout_count;
   logic [PATTERN_COUNT_WIDTH-1:0] rx_align_timeout_count_nxt;
   logic                           rx_align_boundary_check;
   logic                           rx_align_boundary_check_fail;
   logic                           rx_align_matched;

   // Registered counter control signals (reduces combinational fan-in)
   logic                           slide_count_clear_q;  // Clear slide counter
   logic                           slide_count_inc_q;  // Increment slide counter
   logic                           pattern_count_clear_q;  // Clear pattern counter
   logic                           pattern_count_inc_q;  // Increment pattern counter

   // ================================================================
   // Barrel shifter 
   // ================================================================

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         position     <= '0;
         rx_dataout_o <= '0;
         buffer       <= '0;
      end else begin
         buffer       <= {rx_datain_i, buffer[BUFFER_SIZE-1 : DATA_WIDTH]};
         rx_dataout_o <= buffer[BUFFER_SIZE-1-DATA_WIDTH-position-:DATA_WIDTH];

         if (do_slide) begin
            position <= (position == POSITION_WIDTH'(DATA_WIDTH - 1)) ? '0 : position + POSITION_WIDTH'(1);
         end
      end
   end

   // ================================================================
   // Comma detection in encoded domain
   // ================================================================
   // Search for K28.5 (positive or negative disparity) at the LSB-most WORD_SIZE
   // boundary in the barrel-shifter output.

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_data_q <= '0;
      else rx_data_q <= rx_dataout_o;
   end

   always_comb begin
      rx_datan_comma_m_nxt = 1'b0;
      if (rx_data_q[WORD_SIZE-1:0] == COMMA_POS || rx_data_q[WORD_SIZE-1:0] == COMMA_NEG) rx_datan_comma_m_nxt = 1'b1;
   end

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_datan_comma_m <= 1'b0;
      else rx_datan_comma_m <= rx_datan_comma_m_nxt;
   end

   // ================================================================
   // Alignment FSM
   // ================================================================

   // Register FSM transition conditions to reduce combinational fan-in
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         check_to_review_q <= 1'b0;
         check_to_slide_q  <= 1'b0;
         check_to_fail_q   <= 1'b0;
         review_to_done_q  <= 1'b0;
         review_to_fail_q  <= 1'b0;
      end else begin
         // CHECK state transition conditions
         check_to_review_q <= rx_datan_comma_m;
         check_to_slide_q  <= rx_pattern_count_max & ~rx_slide_count_max;
         check_to_fail_q   <= rx_pattern_count_max & rx_slide_count_max;
         // REVIEW state transition conditions
         review_to_done_q  <= rx_align_matched_count_max;
         review_to_fail_q  <= rx_align_boundary_check_fail;
      end
   end

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) fsm <= IDLE;
      else fsm <= fsm_nxt;
   end

   always_comb begin
      case (fsm)
         IDLE:    fsm_nxt = SLIDE;
         SLIDE:   fsm_nxt = CHECK;
         CHECK:   fsm_nxt = check_to_review_q ? REVIEW :
                            check_to_fail_q   ? FAIL   :
                            check_to_slide_q  ? SLIDE  :
                            CHECK;
         REVIEW:  fsm_nxt = review_to_done_q ? DONE :
                            review_to_fail_q ? FAIL :
                            REVIEW;
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
   // Counters
   // ================================================================

   assign rx_slide_count_max = (rx_slide_count == RXSLIDE_COUNT_WIDTH'(RXSLIDE_COUNT_MAX - 1));
   assign rx_pattern_count_max = (rx_pattern_count == PATTERN_COUNT_WIDTH'(TX_PATTERN_LENGTH - 1));

   // Register counter control signals to reduce combinational fan-in
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         slide_count_clear_q   <= 1'b1;
         slide_count_inc_q     <= 1'b0;
         pattern_count_clear_q <= 1'b1;
         pattern_count_inc_q   <= 1'b0;
      end else begin
         // Slide counter controls: clear on idle, comma match, or max both counters; inc on pattern max
         slide_count_clear_q   <= fsm_idle | (fsm_check & rx_datan_comma_m) | (fsm_check & rx_pattern_count_max & rx_slide_count_max);
         slide_count_inc_q     <= fsm_check & rx_pattern_count_max & ~rx_slide_count_max;
         // Pattern counter controls: clear on idle, comma match, or pattern max; inc while checking
         pattern_count_clear_q <= fsm_idle | (fsm_check & rx_datan_comma_m) | (fsm_check & rx_pattern_count_max);
         pattern_count_inc_q   <= fsm_check & ~rx_pattern_count_max & ~rx_datan_comma_m;
      end
   end

   // Slide counter: how many bit positions we have tried
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_slide_count <= '0;
      else rx_slide_count <= rx_slide_count_nxt;
   end

   assign rx_slide_count_nxt = slide_count_clear_q ? RXSLIDE_COUNT_WIDTH'(0) : slide_count_inc_q ? rx_slide_count + RXSLIDE_COUNT_WIDTH'(1) : rx_slide_count;

   // Pattern counter: cycles since last slide (wait for data to propagate)
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_pattern_count <= '0;
      else rx_pattern_count <= rx_pattern_count_nxt;
   end

   assign rx_pattern_count_nxt = pattern_count_clear_q ? PATTERN_COUNT_WIDTH'(0) : pattern_count_inc_q ? rx_pattern_count + PATTERN_COUNT_WIDTH'(1) : rx_pattern_count;

   // ================================================================
   // Alignment verification (REVIEW state)
   // ================================================================

   assign rx_align_matched     = fsm_review & rx_datan_comma_m & rx_align_boundary_check;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_align_matched_count <= '0;
      else rx_align_matched_count <= rx_align_matched_count_nxt;
   end

   assign rx_align_matched_count_nxt = fsm_review ? (rx_align_matched ? rx_align_matched_count + 4'(1) : rx_align_matched_count) : 4'(0);
   assign rx_align_matched_count_max = (rx_align_matched_count == 4'(RX_ALIGN_MATCH_MAX));

   // Timeout counter for periodic boundary checks during REVIEW
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_align_timeout_count <= '0;
      else rx_align_timeout_count <= rx_align_timeout_count_nxt;
   end

   //Starts at 1 due to a 1 cycle pipeline delay between the comma match and the fsm transitioning to REVIEW
   assign rx_align_timeout_count_nxt   = !fsm_review ? PATTERN_COUNT_WIDTH'(1) :
                                         (rx_align_timeout_count == PATTERN_COUNT_WIDTH'(TX_PATTERN_LENGTH - 1)) ? PATTERN_COUNT_WIDTH'(0) :
                                         rx_align_timeout_count + PATTERN_COUNT_WIDTH'(1);
   assign rx_align_boundary_check = (rx_align_timeout_count == PATTERN_COUNT_WIDTH'(TX_PATTERN_LENGTH - 1));
   assign rx_align_boundary_check_fail = rx_align_boundary_check ^ rx_datan_comma_m;

   // ================================================================
   // Output assignments
   // ================================================================

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         align_done_o <= 1'b0;
         align_fail_o <= 1'b0;
      end else begin
         align_done_o <= fsm_done;
         align_fail_o <= fsm_fail;
      end
   end

endmodule  // qeciphy_word_align
