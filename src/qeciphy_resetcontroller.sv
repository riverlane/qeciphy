// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: aniketEng

// Reset sequencing:
// 1. Assert all resets asynchronously when axis_rst_n is asserted.  
// 2. Wait for gt_power_good.  
// 3. Deassert o_gt_rst_n synchronously to the fclk domain after 1250 fclk cycles.  
// 4. Wait for gt_tx_reset_done and gt_rx_reset_done.  
// 5. Deassert o_axis_tx_rst_n and o_axis_rx_rst_n synchronously to the axis_clk domain after an additional 32 axis_clk cycles.  
// 6. Deassert o_tx_rst_n along with o_axis_tx_rst_n but synchronized to the tx_clk domain.  
//    Similarly, deassert o_rx_rst_n along with o_axis_rx_rst_n but synchronized to the rx_clk domain.  


module qeciphy_resetcontroller (
    input  logic axis_clk,
    input  logic axis_rst_n,
    input  logic i_gt_power_good,
    input  logic i_gt_tx_reset_done,
    input  logic i_gt_rx_reset_done,
    output logic o_axis_rx_rst_n,
    output logic o_axis_tx_rst_n,
    output logic o_reset_done,

    input  logic tx_clk,
    output logic o_tx_rst_n,

    input  logic rx_clk,
    output logic o_rx_rst_n,

    input  logic fclk,
    output logic o_gt_rst_n
);

   // -------------------------------------------------------------
   // Type definition
   // -------------------------------------------------------------

   typedef enum bit [2:0] {
      INIT = 0,
      WAIT_FOR_GT_PGOOD = 1,
      GT_RESET = 2,
      WAIT_FOR_RESETDONE = 3,
      TX_RX_RESET = 4,
      DONE = 5,
      UNKNOWN_6 = 6,
      UNKNOWN_7 = 7
   } fsm_t;

   // -------------------------------------------------------------
   // Local declaration
   // -------------------------------------------------------------

   fsm_t fsm, fsm_nxt;

   logic [10:0] fclk_counter;
   logic [10:0] fclk_counter_nxt;
   logic fclk_counter_done;
   logic fclk_counter_done_nxt;
   logic fclk_counter_done_axis;

   logic [4:0] axis_clk_counter;
   logic [4:0] axis_clk_counter_nxt;
   logic axis_clk_counter_done;
   logic axis_clk_counter_done_nxt;

   logic [3:0] rst_stretch_counter;
   logic [3:0] rst_stretch_counter_nxt;
   logic axis_rst_n_int;
   logic axis_rst_n_int_nxt;

   // -------------------------------------------------------------
   // Stretch axis_rst_n
   // -------------------------------------------------------------
   // Reset asynchronously using axis_rst_n.
   // Once the reset is deasserted, it counts for 16 axis_clk cycles before asserting axis_rst_n_int..

   assign rst_stretch_counter_nxt = axis_rst_n_int ? rst_stretch_counter : rst_stretch_counter + 4'h1;

   always_ff @(posedge axis_clk or negedge axis_rst_n) begin
      if (~axis_rst_n) begin
         rst_stretch_counter <= 4'h0;
      end else begin
         rst_stretch_counter <= rst_stretch_counter_nxt;
      end
   end

   assign axis_rst_n_int_nxt = (rst_stretch_counter == 4'hF) ? 1'b1 : axis_rst_n_int;

   always_ff @(posedge axis_clk or negedge axis_rst_n) begin
      if (~axis_rst_n) begin
         axis_rst_n_int <= 1'b0;
      end else begin
         axis_rst_n_int <= axis_rst_n_int_nxt;
      end
   end

   // -------------------------------------------------------------
   // FCLK counter
   // -------------------------------------------------------------
   // Reset asynchronously using axis_rst_n_int.
   // Once the reset is deasserted, it counts for 1250 fclk cycles before asserting counter_done.

   assign fclk_counter_nxt = fclk_counter_done ? fclk_counter : fclk_counter + 11'h1;

   always_ff @(posedge fclk or negedge axis_rst_n_int) begin
      if (~axis_rst_n_int) begin
         fclk_counter <= 11'h0;
      end else begin
         fclk_counter <= fclk_counter_nxt;
      end
   end

   assign fclk_counter_done_nxt = (fclk_counter == 11'd1250) ? 1'b1 : fclk_counter_done;

   always_ff @(posedge fclk or negedge axis_rst_n_int) begin
      if (~axis_rst_n_int) begin
         fclk_counter_done <= 1'b0;
      end else begin
         fclk_counter_done <= fclk_counter_done_nxt;
      end
   end

   // Take the counter done signal from fclk domain to axis_clk domain to notify the state machine.
   riv_synchronizer_2ff i_drp_counter_done_cdc (
       .src_in(fclk_counter_done),
       .dst_clk(axis_clk),
       .dst_rst_n(axis_rst_n_int),
       .dst_out(fclk_counter_done_axis)
   );

   // -------------------------------------------------------------
   // AXIS clock counter
   // -------------------------------------------------------------
   // Reset asynchronously using axis_rst_n_int.
   // The counter runs in TX_RX_RESET state. It counts for 32 axis_clk cycles before asserting counter_done.

   assign axis_clk_counter_nxt = (fsm == TX_RX_RESET) ? axis_clk_counter + 5'h1 : axis_clk_counter;

   always_ff @(posedge axis_clk or negedge axis_rst_n_int) begin
      if (~axis_rst_n_int) begin
         axis_clk_counter <= 5'h0;
      end else begin
         axis_clk_counter <= axis_clk_counter_nxt;
      end
   end

   assign axis_clk_counter_done_nxt = (axis_clk_counter == 5'h1F) ? 1'b1 : axis_clk_counter_done;

   always_ff @(posedge axis_clk or negedge axis_rst_n_int) begin
      if (~axis_rst_n_int) begin
         axis_clk_counter_done <= 1'b0;
      end else begin
         axis_clk_counter_done <= axis_clk_counter_done_nxt;
      end
   end


   // -------------------------------------------------------------
   // State machine
   // -------------------------------------------------------------

   always_ff @(posedge axis_clk or negedge axis_rst_n_int) begin
      if (~axis_rst_n_int) begin
         fsm <= INIT;
      end else begin
         fsm <= fsm_nxt;
      end
   end

   always_comb begin
      unique case (fsm)
         INIT: fsm_nxt = WAIT_FOR_GT_PGOOD;
         WAIT_FOR_GT_PGOOD: fsm_nxt = i_gt_power_good ? GT_RESET : WAIT_FOR_GT_PGOOD;
         GT_RESET: fsm_nxt = fclk_counter_done_axis ? WAIT_FOR_RESETDONE : GT_RESET;
         WAIT_FOR_RESETDONE: fsm_nxt = i_gt_tx_reset_done && i_gt_rx_reset_done ? TX_RX_RESET : WAIT_FOR_RESETDONE;
         TX_RX_RESET: fsm_nxt = axis_clk_counter_done ? DONE : TX_RX_RESET;
         DONE: fsm_nxt = DONE;
         default: fsm_nxt = INIT;
      endcase
   end

   // -------------------------------------------------------------
   // Output generation
   // -------------------------------------------------------------

   // Asserted asynchronously with axis_rst_n_int.Deasserted once the fclk counter completes.
   assign o_gt_rst_n = fclk_counter_done;

   // Asserted asynchronously with axis_rst_n_int.Deasserted once the axis_clk counter completes.  
   assign o_axis_rx_rst_n = axis_clk_counter_done;

   // This is an overlapping reset with the above.
   // Asserted asynchronously with axis_rst_n_int.
   // De-assertion is synchronous to the rx_clk domain.
   riv_synchronizer_2ff i_rx_reset_cdc (
       .src_in(axis_clk_counter_done),
       .dst_clk(rx_clk),
       .dst_rst_n(axis_rst_n_int),
       .dst_out(o_rx_rst_n)
   );

   // Asserted asynchronously with axis_rst_n_int.Deasserted once the axis_clk counter completes.
   assign o_axis_tx_rst_n = axis_clk_counter_done;

   // This is an overlapping reset with the above.
   // Asserted asynchronously with axis_rst_n_int.
   // De-assertion is synchronous to the tx_clk domain.
   riv_synchronizer_2ff i_tx_reset_cdc (
       .src_in(axis_clk_counter_done),
       .dst_clk(tx_clk),
       .dst_rst_n(axis_rst_n_int),
       .dst_out(o_tx_rst_n)
   );

   // Reset done
   always_ff @(posedge axis_clk or negedge axis_rst_n_int) begin
      if (~axis_rst_n_int) begin
         o_reset_done <= 1'b0;
      end else begin
         o_reset_done <= (fsm == DONE);
      end
   end

endmodule  // qeciphy_resetcontroller
