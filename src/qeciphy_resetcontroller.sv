// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// QECIPHY Reset Controller - Multi-Clock Domain Reset Sequencer
//------------------------------------------------------------------------------
// This module orchestrates the proper reset sequence for all QECIPHY components
// across multiple asynchronous clock domains. It implements a simplified two-stage
// reset release strategy following GT transceiver requirements.
//
// Reset Sequence Flow:
// 1. Wait for GT power supplies to stabilize (gt_power_good_i)
// 2. Delay 1250 f_clk_i cycles (GT timing requirement)
// 3. Release GT transceiver reset (gt_rst_n_o)
// 4. Wait for GT TX/RX reset completion (gt_tx_rst_done_i, gt_rx_rst_done_i)
// 5. Delay 32 axis_clk_i cycles
// 6. Release all datapath resets simultaneously
// 7. Assert reset sequence completion (rst_done_o)
//
// Clock Domain Management:
// - State machine runs in AXIS clock domain (primary system clock)
// - Reset deassertion is synchronized to each destination clock domain
// - GT timing requirements handled in f_clk_i domain
// - Cross-domain synchronization prevents metastability
//------------------------------------------------------------------------------

module qeciphy_resetcontroller (
    // =========================================================================
    // AXIS Clock Domain Interface (Primary Reset Control)
    // =========================================================================
    input  logic axis_clk_i,             // Primary AXIS clock
    input  logic async_rst_n_i,          // Master reset input (active-low)
    input  logic gt_power_good_i,        // GT power supply ready indicator
    input  logic gt_tx_rst_done_i,       // GT TX reset sequence complete
    input  logic gt_rx_rst_done_i,       // GT RX reset sequence complete
    output logic axis_rst_n_o,           // async_rst_n_i reflected in AXIS domain
    output logic axis_datapath_rst_n_o,  // AXIS datapath reset output
    output logic rst_done_o,             // Reset sequence complete

    // =========================================================================
    // TX Clock Domain Interface
    // =========================================================================
    input  logic tx_clk_i,            // TX clock
    output logic tx_rst_n_o,          // async_rst_n_i reflected in TX domain
    output logic tx_datapath_rst_n_o, // TX datapath reset output

    // =========================================================================
    // RX Clock Domain Interface
    // =========================================================================
    input  logic rx_clk_i,            // RX clock
    output logic rx_rst_n_o,          // async_rst_n_i reflected in RX domain
    output logic rx_datapath_rst_n_o, // RX datapath reset output

    // =========================================================================
    // Fabric Clock Domain Interface
    // =========================================================================
    input  logic f_clk_i,    // Free-running clock
    output logic f_rst_n_o,  // async_rst_n_i reflected in free running domain
    output logic gt_rst_n_o  // GT transceiver reset
);

   // =========================================================================
   // Reset Sequence State Machine Definition
   // =========================================================================
   // State bits [6:7] directly control reset output levels during sequence.

   typedef enum logic [7:0] {
      RESET                         = 8'b00000001,  // [0] Initial state: all resets asserted
      WAIT_GT_PWRGOOD               = 8'b00000010,  // [1] Wait for GT power supplies ready
      DELAY_BEFORE_GT_RELEASE       = 8'b00000100,  // [2] GT timing delay (1250 f_clk_i cycles)
      RELEASE_GT_RST                = 8'b01000000,  // [6] Release GT reset, enable GT operation
      WAIT_GT_RESET_DONE            = 8'b01001000,  // [6,3] Wait for GT TX/RX reset completion
      DELAY_BEFORE_DATAPATH_RELEASE = 8'b01010000,  // [6,4] 32 axis_clk_i cycles delay before datapath release
      RELEASE_DATAPATH              = 8'b11000000,  // [6,7] Release all datapath resets simultaneously
      DONE                          = 8'b11100000   // [6,7,5] All resets released, sequence complete
   } fsm_t;

   // =========================================================================
   // Internal Signal Declarations
   // =========================================================================

   // State machine control
   fsm_t state, state_nxt;  // Current and next state registers

   // State decoders
   logic        in_gt_delay_state;
   logic        in_datapath_delay_state;
   logic        in_done_state;

   // GT timing delay management
   logic        in_gt_delay_state_fclk;  // GT delay state synchronized to f_clk_i domain
   logic [10:0] gt_delay_counter_fclk;  // 1250-cycle countdown timer (f_clk_i)
   logic        gt_delay_done_fclk;  // Delay completion flag (f_clk_i)
   logic        gt_delay_done;  // Delay completion flag (axis_clk_i)

   // Datapath delay management
   logic [ 4:0] datapath_delay_counter;  // 32-cycle countdown timer (axis_clk_i)
   logic        datapath_delay_done;  // Delay completion flag (axis_clk_i)

   // Reset level control signals (decoded from state bits)
   logic        gt_rst_state;
   logic        axis_datapath_rst_state;

   // async_rst_n_i reflected in other clock domains
   logic        f_rst_n;
   logic        rx_rst_n;
   logic        tx_rst_n;
   logic        axis_rst_n;

   // =========================================================================
   // Cross-Domain Reset Synchronization
   // =========================================================================

   assign f_rst_n_o = f_rst_n;
   assign rx_rst_n_o = rx_rst_n;
   assign tx_rst_n_o = tx_rst_n;
   assign axis_rst_n_o = axis_rst_n;

   // Synchronize reset release to fabric clock domain
   riv_synchronizer_2ff #(
       .RESET_TYPE("ASYNC")
   ) i_fclk_rst_cdc (
       .src_in   (1'b1),
       .dst_clk  (f_clk_i),
       .dst_rst_n(async_rst_n_i),
       .dst_out  (f_rst_n)
   );

   // Synchronize reset release to RX clock domain
   riv_synchronizer_2ff #(
       .RESET_TYPE("ASYNC")
   ) i_rx_clk_rst_cdc (
       .src_in   (1'b1),
       .dst_clk  (rx_clk_i),
       .dst_rst_n(async_rst_n_i),
       .dst_out  (rx_rst_n)
   );

   // Synchronize reset release to TX clock domain  
   riv_synchronizer_2ff #(
       .RESET_TYPE("ASYNC")
   ) i_tx_clk_rst_cdc (
       .src_in   (1'b1),
       .dst_clk  (tx_clk_i),
       .dst_rst_n(async_rst_n_i),
       .dst_out  (tx_rst_n)
   );

   // Synchronize reset release to AXIS clock domain
   riv_synchronizer_2ff #(
       .RESET_TYPE("ASYNC")
   ) i_axis_clk_rst_cdc (
       .src_in   (1'b1),
       .dst_clk  (axis_clk_i),
       .dst_rst_n(async_rst_n_i),
       .dst_out  (axis_rst_n)
   );

   // =========================================================================
   // State Machine Decoders
   // =========================================================================

   assign in_gt_delay_state = state[2];
   assign in_datapath_delay_state = state[4];
   assign in_done_state = state[5];
   assign gt_rst_state = state[6];
   assign axis_datapath_rst_state = state[7];

   // =========================================================================
   // GT Timing Delay Counter
   // =========================================================================
   // GT transceivers require 1250 fabric clock cycles between power good
   // and reset deassertion for proper initialization.

   // Cross GT delay state to fabric clock domain
   riv_synchronizer_2ff i_cdc_in_gt_delay_state_fclk (
       .src_in   (in_gt_delay_state),
       .dst_clk  (f_clk_i),
       .dst_rst_n(f_rst_n),
       .dst_out  (in_gt_delay_state_fclk)
   );

   // GT delay countdown counter
   always_ff @(posedge f_clk_i) begin
      if (!f_rst_n) begin
         gt_delay_counter_fclk <= 11'd1249;
      end else if (in_gt_delay_state_fclk) begin
         gt_delay_counter_fclk <= gt_delay_counter_fclk - 11'd1;
      end
   end

   // GT delay completion
   always_ff @(posedge f_clk_i) begin
      if (!f_rst_n) begin
         gt_delay_done_fclk <= 1'b0;
      end else if (~|gt_delay_counter_fclk) begin
         gt_delay_done_fclk <= 1'b1;
      end
   end

   // Cross GT delay completion back to AXIS clock domain
   riv_synchronizer_2ff i_cdc_gt_delay_done (
       .src_in   (gt_delay_done_fclk),
       .dst_clk  (axis_clk_i),
       .dst_rst_n(axis_rst_n),
       .dst_out  (gt_delay_done)
   );

   // =========================================================================
   // Datapath Delay Counter
   // =========================================================================
   // Provide 32 AXIS clock cycles between GT ready and datapath reset release.

   // Datapath delay countdown counter
   always_ff @(posedge axis_clk_i) begin
      if (!axis_rst_n) begin
         datapath_delay_counter <= 5'd31;
      end else if (in_datapath_delay_state) begin
         datapath_delay_counter <= datapath_delay_counter - 5'd1;
      end
   end

   // Datapath delay completion
   always_ff @(posedge axis_clk_i) begin
      if (!axis_rst_n) begin
         datapath_delay_done <= 1'b0;
      end else if (~|datapath_delay_counter) begin
         datapath_delay_done <= 1'b1;
      end
   end

   // =========================================================================
   // Reset Sequence State Machine (AXIS Clock Domain)
   // =========================================================================

   // State register
   always_ff @(posedge axis_clk_i) begin
      if (!axis_rst_n) begin
         state <= RESET;
      end else begin
         state <= state_nxt;
      end
   end

   // Next-state logic: implements the simplified reset sequence flow
   always_comb begin
      case (state)
         RESET:                         state_nxt = WAIT_GT_PWRGOOD;
         WAIT_GT_PWRGOOD:               state_nxt = gt_power_good_i ? DELAY_BEFORE_GT_RELEASE : WAIT_GT_PWRGOOD;
         DELAY_BEFORE_GT_RELEASE:       state_nxt = gt_delay_done ? RELEASE_GT_RST : DELAY_BEFORE_GT_RELEASE;
         RELEASE_GT_RST:                state_nxt = WAIT_GT_RESET_DONE;
         WAIT_GT_RESET_DONE:            state_nxt = (gt_tx_rst_done_i && gt_rx_rst_done_i) ? DELAY_BEFORE_DATAPATH_RELEASE : WAIT_GT_RESET_DONE;
         DELAY_BEFORE_DATAPATH_RELEASE: state_nxt = datapath_delay_done ? RELEASE_DATAPATH : DELAY_BEFORE_DATAPATH_RELEASE;
         RELEASE_DATAPATH:              state_nxt = DONE;
         DONE:                          state_nxt = DONE;
         default:                       state_nxt = RESET;
      endcase
   end

   // =========================================================================
   // Outputs
   // =========================================================================

   // Reset sequence completion indicator
   assign rst_done_o = in_done_state;

   // GT transceiver reset (synchronized to fabric clock domain)
   riv_synchronizer_2ff i_cdc_gt_rst_n_o (
       .src_in   (gt_rst_state),
       .dst_clk  (f_clk_i),
       .dst_rst_n(f_rst_n),
       .dst_out  (gt_rst_n_o)
   );

   // AXIS datapath reset
   assign axis_datapath_rst_n_o = axis_datapath_rst_state;

   // TX datapath reset (synchronized to TX clock domain)
   riv_synchronizer_2ff i_cdc_tx_ch_enc_rst_n_o (
       .src_in   (axis_datapath_rst_state),
       .dst_clk  (tx_clk_i),
       .dst_rst_n(tx_rst_n),
       .dst_out  (tx_datapath_rst_n_o)
   );

   // RX datapath reset (synchronized to RX clock domain)
   riv_synchronizer_2ff i_cdc_rx_ch_dec_rst_n_o (
       .src_in   (axis_datapath_rst_state),
       .dst_clk  (rx_clk_i),
       .dst_rst_n(rx_rst_n),
       .dst_out  (rx_datapath_rst_n_o)
   );

endmodule  // qeciphy_resetcontroller
