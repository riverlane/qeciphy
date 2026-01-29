// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Kauser Johar

module qeciphy_rx_bytealigner #(
    parameter integer RX_DATA_WIDTH     = 32,
    parameter integer TX_PATTERN_LENGTH = 6
) (
    input  logic                     clk_i,
    input  logic                     rst_n_i,
    input  logic                     slide_rdy_i,
    input  logic [RX_DATA_WIDTH-1:0] tdata_i,
    output logic                     slide_o,
    output logic                     align_done_o,
    output logic                     align_fail_o
);

   // -------------------------------------------------------------
   // Local parameters and type definition
   // -------------------------------------------------------------

   typedef enum logic [2:0] {
      IDLE   = 3'h1,
      SLIDE0 = 3'h2,
      SLIDE1 = 3'h3,
      OFF    = 3'h4,
      CHECK  = 3'h5,
      REVIEW = 3'h0,
      DONE   = 3'h6,
      FAIL   = 3'h7
   } fsm_t;

   // Comma character mask
   localparam RXSLIDE_COUNT_MAX = 80;
   localparam RXSLIDE_COUNT_WIDTH = $clog2(RXSLIDE_COUNT_MAX);
   localparam RXSLIDE_IDLE_CYCLES = 32;  // "RXSLIDE must be deasserted for more than 32 RXUSRCLK2 cycles..." UG578 page:249
   localparam PATTERN_COUNT_WIDTH = $clog2(TX_PATTERN_LENGTH);
   localparam RX_ALIGN_MATCH_MAX = 4'd8;
   localparam RX_ALIGN_COUNTER_WIDTH = $clog2(TX_PATTERN_LENGTH);

   // -------------------------------------------------------------
   // Declaration
   // -------------------------------------------------------------

   fsm_t                              fsm;
   fsm_t                              fsm_nxt;
   logic                              fsm_idle;
   logic                              fsm_check;
   logic                              fsm_review;
   logic                              fsm_slide0;
   logic                              fsm_slide1;
   logic                              fsm_off;
   logic                              fsm_done;
   logic                              fsm_fail;
   logic [     RXSLIDE_COUNT_WIDTH:0] rx_slide_count;
   logic [     RXSLIDE_COUNT_WIDTH:0] rx_slide_count_nxt;
   logic [                       5:0] rx_slide_idle_count;
   logic [                       5:0] rx_slide_idle_count_nxt;
   logic [     PATTERN_COUNT_WIDTH:0] rx_pattern_count;
   logic [     PATTERN_COUNT_WIDTH:0] rx_pattern_count_nxt;
   logic                              rx_slide_count_max;
   logic                              rx_slide_idle_count_max;
   logic                              rx_pattern_count_max;
   logic                              rx_datan_comma_m;
   logic [                       3:0] rx_align_matched_count;
   logic [                       3:0] rx_align_matched_count_nxt;
   logic                              rx_align_matched_count_max;
   logic [RX_ALIGN_COUNTER_WIDTH-1:0] rx_align_timeout_count;
   logic [RX_ALIGN_COUNTER_WIDTH-1:0] rx_align_timeout_count_nxt;
   logic                              rx_align_boundary_check;
   logic                              rx_align_boundary_check_fail;
   logic [                      31:0] rx_data;
   logic                              rx_align_matched;

   // -------------------------------------------------------------
   // Hit logic
   // -------------------------------------------------------------

   assign rx_slide_idle_count_max = rx_slide_idle_count == RXSLIDE_IDLE_CYCLES - 1;
   assign rx_pattern_count_max    = rx_pattern_count == TX_PATTERN_LENGTH[PATTERN_COUNT_WIDTH:0] - 1;
   assign rx_slide_count_max      = rx_slide_count == RXSLIDE_COUNT_MAX[RXSLIDE_COUNT_WIDTH:0] - 1;
   assign rx_datan_comma_m        = rx_data == 32'h000000BC;

   always_ff @(posedge clk_i) begin
      rx_data <= tdata_i;
   end

   // -------------------------------------------------------------
   // FSM states
   // -------------------------------------------------------------

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) fsm <= IDLE;
      else fsm <= fsm_nxt;
   end

   always_comb begin
      case (fsm)
         IDLE: fsm_nxt = slide_rdy_i ? SLIDE0 : IDLE;
         SLIDE0: fsm_nxt = SLIDE1;
         SLIDE1: fsm_nxt = OFF;
         OFF: fsm_nxt = slide_rdy_i & rx_slide_idle_count_max ? CHECK : OFF;
         CHECK: fsm_nxt = rx_datan_comma_m ? REVIEW : rx_pattern_count_max ? (rx_slide_count_max ? FAIL : SLIDE0) : CHECK;
         REVIEW:
         fsm_nxt =  // Check that after the first successful hit for comma character
                    // we are able to match it for at least 8 consecutive times before proceeding
                    // to DONE state
         rx_align_matched_count_max ? DONE : rx_align_boundary_check_fail ? FAIL : REVIEW;
         DONE: fsm_nxt = DONE;
         FAIL: fsm_nxt = IDLE;  // Once failed, retry.
         default: fsm_nxt = fsm_t'(1'bx);
      endcase  // case (fsm)
   end  // always_comb

   assign fsm_idle   = fsm==IDLE;
   assign fsm_check  = fsm==CHECK;
   assign fsm_review = fsm==REVIEW;
   assign fsm_slide0 = fsm==SLIDE0;
   assign fsm_slide1 = fsm==SLIDE1;
   assign fsm_off    = fsm==OFF;
   assign fsm_done   = fsm==DONE;
   assign fsm_fail   = fsm==FAIL;

   // -------------------------------------------------------------
   // Counters
   // -------------------------------------------------------------

   // Slide idle counter
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_slide_idle_count <= 'h0;
      else rx_slide_idle_count <= rx_slide_idle_count_nxt;
   end

   assign rx_slide_idle_count_nxt = fsm_idle ? 'h0 : fsm_off & rx_slide_idle_count_max & slide_rdy_i ? 'h0 : fsm_off ? rx_slide_idle_count + 'h1 : rx_slide_idle_count;

   // Slide counter
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_slide_count <= 'h0;
      else rx_slide_count <= rx_slide_count_nxt;
   end

   assign rx_slide_count_nxt = fsm_idle                                              ? 'h0 :
                              fsm_check & rx_pattern_count_max & rx_slide_count_max ? 'h0 :
                              fsm_check & rx_pattern_count_max                      ? rx_slide_count + 'h1 :
                              fsm_check & rx_datan_comma_m                    ? 'h0 :
                                                                                      rx_slide_count;

   // Pattern counter
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_pattern_count <= 'h0;
      else rx_pattern_count <= rx_pattern_count_nxt;
   end

   assign rx_pattern_count_nxt = fsm_idle ? 'h0 : fsm_check & rx_pattern_count_max ? 'h0 : fsm_check & rx_datan_comma_m ? 'h0 : fsm_check ? rx_pattern_count + 'h1 : rx_pattern_count;

   // -------------------------------------------------------------
   // Link drop detection
   // -------------------------------------------------------------

   // Matched counter
   assign rx_align_matched     = fsm_review & rx_datan_comma_m & rx_align_boundary_check;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_align_matched_count <= 'h0;
      else rx_align_matched_count <= rx_align_matched_count_nxt;
   end

   assign rx_align_matched_count_nxt = fsm_review ? (rx_align_matched ? rx_align_matched_count + 'h1 : rx_align_matched_count) : 'h0;

   assign rx_align_matched_count_max = rx_align_matched_count == RX_ALIGN_MATCH_MAX;

   // Timeout counter

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) rx_align_timeout_count <= 'h0;
      else rx_align_timeout_count <= rx_align_timeout_count_nxt;
   end

   // The timout counter is used for the purposes of timeout in
   // REVIEW state
   assign rx_align_timeout_count_nxt = fsm_review ? rx_align_timeout_count + 'h1 : 'h0;

   assign rx_align_boundary_check = rx_align_timeout_count == '1;
   assign rx_align_boundary_check_fail = rx_align_boundary_check ^ rx_datan_comma_m;

   // -------------------------------------------------------------
   // Output assignments
   // -------------------------------------------------------------

   assign slide_o = fsm_slide0 | fsm_slide1;

   // Flopped outputs
   always_ff @(posedge clk_i) begin
      align_done_o <= fsm_done;
      align_fail_o <= fsm_fail;
   end

endmodule  // qeciphy_rx_bytealigner
