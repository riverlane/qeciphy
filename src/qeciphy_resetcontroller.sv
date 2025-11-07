// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// QECIPHY Reset Controller
//------------------------------------------------------------------------------
// This module implements a comprehensive reset sequencing controller for the
// QECIPHY. It manages the proper startup and reset sequence
// for Xilinx GT transceivers and associated logic across multiple clock domains.
//
// The reset controller ensures proper timing relationships between:
// - GT power good signals
// - GT reset assertion/deassertion  
// - AXI4-Stream interface resets
// - User logic resets
//
// Reset Sequence:
// 1. Assert all resets asynchronously when axis_rst_n is asserted
// 2. Wait for gt_power_good to be asserted
// 3. Deassert o_gt_rst_n after 1250 fclk cycles (GT reset timing requirement)
// 4. Wait for gt_tx_reset_done and gt_rx_reset_done 
// 5. Deassert o_axis_tx_rst_n and o_axis_rx_rst_n after 32 axis_clk cycles
// 6. Synchronously deassert o_tx_rst_n and o_rx_rst_n to their respective domains
// 7. Assert o_reset_done to indicate complete reset sequence
//
// Clock Domains:
// - axis_clk: Main AXI4-Stream clock domain (state machine, counters)
// - fclk: Free-running reference clock (GT reset timing)
// - tx_clk: GT transmitter recovered clock
// - rx_clk: GT receiver recovered clock
//
//------------------------------------------------------------------------------

module qeciphy_resetcontroller (
    // Main clock domain (AXI4-Stream)
    input logic axis_clk,   // AXI4-Stream clock
    input logic axis_rst_n, // Active-low reset (master reset)

    // GT status inputs
    input logic i_gt_power_good,     // GT power good indicator
    input logic i_gt_tx_reset_done,  // GT TX reset complete
    input logic i_gt_rx_reset_done,  // GT RX reset complete

    // AXI4-Stream reset outputs
    output logic o_axis_rx_rst_n,  // AXI4-Stream RX reset (axis_clk domain)
    output logic o_axis_tx_rst_n,  // AXI4-Stream TX reset (axis_clk domain)
    output logic o_reset_done,     // Reset sequence complete indicator

    // GT transmitter clock domain
    input  logic tx_clk,     // GT TX recovered clock
    output logic o_tx_rst_n, // TX logic reset (tx_clk domain)

    // GT receiver clock domain  
    input  logic rx_clk,     // GT RX recovered clock
    output logic o_rx_rst_n, // RX logic reset (rx_clk domain)

    // GT reference clock domain
    input  logic fclk,       // Free-running reference clock
    output logic o_gt_rst_n  // GT reset (fclk domain)
);

   //--------------------------------------------------------------------------
   // State Machine Type Definition
   //--------------------------------------------------------------------------

   typedef enum bit [2:0] {
      INIT          = 0,  // Initial state: all resets asserted, counters loaded
      WAIT_GT_POWER = 1,  // Waiting for GT power good signal
      GT_RESET      = 2,  // GT reset delay: counting 1250 fclk cycles
      WAIT_GT_READY = 3,  // Waiting for GT TX/RX reset done signals
      TX_RX_RESET   = 4,  // TX/RX reset delay: counting 32 axis_clk cycles  
      DONE          = 5,  // Reset sequence complete: all resets released
      RESERVED_6    = 6,  // Reserved for future use
      RESERVED_7    = 7   // Reserved for future use
   } fsm_t;

   //--------------------------------------------------------------------------
   // Internal Signal Declarations
   //--------------------------------------------------------------------------

   // State machine signals
   fsm_t fsm, fsm_nxt;  // Current and next state

   // Counter completion signals
   logic fclk_counter_done;
   logic fclk_counter_done_axis;
   logic axis_clk_counter_done;

   // State machine status signals for cross-domain use
   logic fsm_init;
   logic fsm_gt_reset;
   logic fsm_tx_rx_reset;
   logic fsm_gt_reset_fclk;
   logic fsm_init_fclk;

   // Reset domain crossing outputs
   logic fclk_rst_n;
   logic rx_clk_rst_n;
   logic tx_clk_rst_n;

   //--------------------------------------------------------------------------
   // Reset Domain Crossing Synchronizers
   //--------------------------------------------------------------------------
   // Generate reset release signals synchronized to each clock domain.
   // These ensure proper reset deassertion timing in each domain.

   // Synchronize reset deassertion to fclk domain
   riv_synchronizer_2ff i_fclk_rst_cdc (
       .src_in   (1'b1),
       .dst_clk  (fclk),
       .dst_rst_n(axis_rst_n),
       .dst_out  (fclk_rst_n)
   );

   // Synchronize reset deassertion to rx_clk domain
   riv_synchronizer_2ff i_rx_clk_rst_cdc (
       .src_in   (1'b1),
       .dst_clk  (rx_clk),
       .dst_rst_n(axis_rst_n),
       .dst_out  (rx_clk_rst_n)
   );

   // Synchronize reset deassertion to tx_clk domain  
   riv_synchronizer_2ff i_tx_clk_rst_cdc (
       .src_in   (1'b1),
       .dst_clk  (tx_clk),
       .dst_rst_n(axis_rst_n),
       .dst_out  (tx_clk_rst_n)
   );

   //--------------------------------------------------------------------------
   // FCLK Domain Counter (GT Reset Timing)
   //--------------------------------------------------------------------------
   // Implements the required 1250 fclk cycle delay before deasserting GT reset.
   // This timing requirement ensures proper GT initialization per Xilinx specs.
   //
   // The counter:
   // - Loads with 1250 when FSM enters INIT state
   // - Counts down when FSM is in GT_RESET state  
   // - Completion signal crosses back to axis_clk for state machine

   assign fsm_init     = (fsm == INIT);
   assign fsm_gt_reset = (fsm == GT_RESET);

   // Synchronize state machine status to fclk domain
   riv_synchronizer_2ff i_fsm_init_cdc (
       .src_in   (fsm_init),
       .dst_clk  (fclk),
       .dst_rst_n(fclk_rst_n),
       .dst_out  (fsm_init_fclk)
   );

   riv_synchronizer_2ff i_fsm_gt_reset_cdc (
       .src_in   (fsm_gt_reset),
       .dst_clk  (fclk),
       .dst_rst_n(fclk_rst_n),
       .dst_out  (fsm_gt_reset_fclk)
   );

   // GT reset timing counter (1250 fclk cycles)
   riv_counter #(
       .WIDTH(11)
   ) i_fclk_counter (
       .clk   (fclk),
       .rst_n (fclk_rst_n),
       .value (11'd1250),
       .load  (fsm_init_fclk),
       .enable(~fclk_counter_done && fsm_gt_reset_fclk),
       .done  (fclk_counter_done)
   );

   // Cross counter completion signal back to axis_clk domain for state machine
   riv_synchronizer_2ff i_drp_counter_done_cdc (
       .src_in   (fclk_counter_done),
       .dst_clk  (axis_clk),
       .dst_rst_n(axis_rst_n),
       .dst_out  (fclk_counter_done_axis)
   );

   //--------------------------------------------------------------------------
   // AXIS Clock Domain Counter (TX/RX Reset Timing)  
   //--------------------------------------------------------------------------
   // Implements the required 32 axis_clk cycle delay before deasserting
   // AXI4-Stream TX/RX resets.
   //
   // The counter:
   // - Loads with 31 when FSM enters INIT state
   // - Counts down when FSM is in TX_RX_RESET state
   // - Completion enables deassertion of AXI4-Stream resets

   // Register the TX_RX_RESET state for counter enable
   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) begin
         fsm_tx_rx_reset <= 1'b0;
      end else begin
         fsm_tx_rx_reset <= (fsm == TX_RX_RESET);
      end
   end

   // AXI4-Stream reset timing counter (32 axis_clk cycles)
   riv_counter #(
       .WIDTH(5)
   ) i_axis_clk_counter (
       .clk   (axis_clk),
       .rst_n (axis_rst_n),
       .value (5'd31),
       .load  (fsm_init),
       .enable(~axis_clk_counter_done && fsm_tx_rx_reset),
       .done  (axis_clk_counter_done)
   );


   //--------------------------------------------------------------------------
   // Reset Sequencing State Machine
   //--------------------------------------------------------------------------
   // Controls the overall reset sequence timing and coordination.
   // Operates synchronously in the axis_clk domain and coordinates with
   // counters and status signals from other clock domains.

   // State machine register (synchronous reset)
   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) begin
         fsm <= INIT;
      end else begin
         fsm <= fsm_nxt;
      end
   end

   // State machine next-state logic
   always_comb begin
      unique case (fsm)
         // INIT: Wait for both counters to be loaded
         INIT: begin
            fsm_nxt = (~fclk_counter_done_axis && ~axis_clk_counter_done) ? WAIT_GT_POWER : INIT;
         end

         // WAIT_GT_POWER: Wait for GT power good signal
         WAIT_GT_POWER: begin
            fsm_nxt = i_gt_power_good ? GT_RESET : WAIT_GT_POWER;
         end

         // GT_RESET: Wait for fclk counter to complete (1250 cycles)
         GT_RESET: begin
            fsm_nxt = fclk_counter_done_axis ? WAIT_GT_READY : GT_RESET;
         end

         // WAIT_GT_READY: Wait for both GT TX and RX to complete reset
         WAIT_GT_READY: begin
            fsm_nxt = (i_gt_tx_reset_done && i_gt_rx_reset_done) ? TX_RX_RESET : WAIT_GT_READY;
         end

         // TX_RX_RESET: Wait for axis_clk counter to complete (32 cycles)
         TX_RX_RESET: begin
            fsm_nxt = axis_clk_counter_done ? DONE : TX_RX_RESET;
         end

         // DONE: Reset sequence complete, stay in this state
         DONE: begin
            fsm_nxt = DONE;
         end

         // Default: Return to INIT on unexpected states
         default: begin
            fsm_nxt = INIT;
         end
      endcase
   end

   //--------------------------------------------------------------------------
   // Reset Output Generation
   //--------------------------------------------------------------------------
   // Generates all reset outputs with proper timing and domain synchronization.
   // All resets are asserted asynchronously when axis_rst_n is asserted,
   // but deasserted synchronously according to the reset sequence.

   // GT Reset (fclk domain)
   assign o_gt_rst_n = fclk_counter_done;

   // AXI4-Stream RX Reset (axis_clk domain)  
   assign o_axis_rx_rst_n = axis_clk_counter_done;

   // RX Logic Reset (rx_clk domain)
   // Synchronized version of AXI4-Stream RX reset for rx_clk domain logic
   riv_synchronizer_2ff i_rx_reset_cdc (
       .src_in   (axis_clk_counter_done),
       .dst_clk  (rx_clk),
       .dst_rst_n(axis_rst_n),
       .dst_out  (o_rx_rst_n)
   );

   // AXI4-Stream TX Reset (axis_clk domain)
   assign o_axis_tx_rst_n = axis_clk_counter_done;

   // TX Logic Reset (tx_clk domain)
   // Synchronized version of AXI4-Stream TX reset for tx_clk domain logic
   riv_synchronizer_2ff i_tx_reset_cdc (
       .src_in   (axis_clk_counter_done),
       .dst_clk  (tx_clk),
       .dst_rst_n(axis_rst_n),
       .dst_out  (o_tx_rst_n)
   );

   // Reset Done Indicator
   // Asserted when the complete reset sequence is finished
   always_ff @(posedge axis_clk or negedge axis_rst_n) begin
      if (~axis_rst_n) begin
         o_reset_done <= 1'b0;
      end else begin
         o_reset_done <= (fsm == DONE);
      end
   end

endmodule  // qeciphy_resetcontroller
