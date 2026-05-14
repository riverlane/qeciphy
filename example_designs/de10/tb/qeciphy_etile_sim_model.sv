// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
//
// Behavioral simulation model for the Intel Agilex E-Tile Direct PHY IP.
// Replaces qeciphy_etile when `ETILE_SIM_MODEL is defined.
//
// Port interface is identical to qeciphy_etile plus two sim-only ports:
//   sim_tx_parallel_data_o  — expose TX parallel data for testbench cross-connect
//   sim_rx_parallel_data_i  — receive peer TX parallel data from testbench
//
// The parent (qeciphy_gt_altera) declares local logic signals
// sim_etile_rx_parallel_data and connects it to sim_rx_parallel_data_i.
// The testbench drives that signal hierarchically from the peer's
// transceiver_inst.sim_tx_parallel_data_o.

`timescale 1ps / 1ps

module qeciphy_etile_sim_model #(
    // Half-period of generated TX/RX clocks.
    // Default: 1600 ps = 312.5 MHz (2x 156.25 MHz reference).
    parameter real SIM_CLK_HALF_PERIOD_PS = 1600.0,
    // Cycles from reset deassert to *_pma_ready assertion.
    parameter int  PMA_READY_CYCLES       = 8,
    // Cycles from reset deassert to *_ready assertion.
    parameter int  READY_CYCLES           = 16
) (
    // Reference clock input (unused in sim; clocks are self-generated)
    input logic pll_refclk0,

    // Unified reset (active-high; drives both TX and RX channels)
    input logic reset,

    // TX status outputs
    output logic tx_ready,
    output logic tx_pma_ready,

    // RX status outputs
    output logic rx_ready,
    output logic rx_pma_ready,

    // Parallel clock inputs (fed back from qeciphy_altera_clk_mmcm outputs)
    input logic tx_coreclkin,
    input logic rx_coreclkin,

    // Clock outputs (drive qeciphy_altera_clk_mmcm inputs)
    output logic tx_clkout,
    output logic tx_clkout2,
    output logic rx_clkout,
    output logic rx_clkout2,

    // Serial data (tied to constants; unused in sim)
    output logic tx_serial_data,
    output logic tx_serial_data_n,
    input  logic rx_serial_data,
    input  logic rx_serial_data_n,

    // Lock status
    output logic rx_is_lockedtodata,

    // Parallel data
    input  logic [79:0] tx_parallel_data,
    output logic [79:0] rx_parallel_data,

    // Sim-only parallel crossconnect ports
    output logic [79:0] sim_tx_parallel_data_o,
    input  logic [79:0] sim_rx_parallel_data_i
);

   // ----------------------------------------------------------------
   // Clock generation
   // ----------------------------------------------------------------
   // tx_clkout2 / rx_clkout2 are the master clock sources; they are
   // routed through qeciphy_altera_clk_mmcm (div1x passthrough) and
   // fed back into tx_coreclkin / rx_coreclkin.

   initial tx_clkout2 = 1'b0;
   always #(SIM_CLK_HALF_PERIOD_PS) tx_clkout2 = ~tx_clkout2;

   initial rx_clkout2 = 1'b0;
   always #(SIM_CLK_HALF_PERIOD_PS) rx_clkout2 = ~rx_clkout2;

   assign tx_clkout = tx_clkout2;
   assign rx_clkout = rx_clkout2;

   // ----------------------------------------------------------------
   // Reset FSM type (shared by TX and RX channels)
   // ----------------------------------------------------------------
   // E-Tile has no reset-ack handshake; the core simply polls *_ready.
   typedef enum logic [1:0] {
      RESETTING  = 2'b00,  // reset asserted: outputs deasserted
      WAIT_READY = 2'b01,  // reset released: counting up to ready
      READY_ST   = 2'b10   // fully operational
   } etile_state_t;

   // ----------------------------------------------------------------
   // TX reset FSM  (clocked on tx_coreclkin)
   // ----------------------------------------------------------------
   etile_state_t tx_state;
   int unsigned  tx_cnt;

   initial begin
      tx_state     = RESETTING;
      tx_cnt       = 0;
      tx_ready     = 1'b0;
      tx_pma_ready = 1'b0;
   end

   always_ff @(posedge tx_coreclkin) begin
      case (tx_state)
         RESETTING: begin
            tx_ready     <= 1'b0;
            tx_pma_ready <= 1'b0;
            tx_cnt       <= 0;
            if (!reset) begin
               tx_state <= WAIT_READY;
            end
         end

         WAIT_READY: begin
            if (reset) begin
               tx_state <= RESETTING;
            end else begin
               tx_cnt <= tx_cnt + 1;
               if (tx_cnt == PMA_READY_CYCLES - 1) begin
                  tx_pma_ready <= 1'b1;
               end
               if (tx_cnt == READY_CYCLES - 1) begin
                  tx_ready <= 1'b1;
                  tx_state <= READY_ST;
               end
            end
         end

         READY_ST: begin
            if (reset) begin
               tx_state     <= RESETTING;
               tx_ready     <= 1'b0;
               tx_pma_ready <= 1'b0;
               tx_cnt       <= 0;
            end
         end

         default: tx_state <= RESETTING;
      endcase
   end

   // ----------------------------------------------------------------
   // RX reset FSM  (clocked on rx_coreclkin)
   // ----------------------------------------------------------------
   etile_state_t rx_state;
   int unsigned  rx_cnt;

   initial begin
      rx_state           = RESETTING;
      rx_cnt             = 0;
      rx_ready           = 1'b0;
      rx_pma_ready       = 1'b0;
      rx_is_lockedtodata = 1'b0;
   end

   always_ff @(posedge rx_coreclkin) begin
      case (rx_state)
         RESETTING: begin
            rx_ready           <= 1'b0;
            rx_pma_ready       <= 1'b0;
            rx_is_lockedtodata <= 1'b0;
            rx_cnt             <= 0;
            if (!reset) begin
               rx_state <= WAIT_READY;
            end
         end

         WAIT_READY: begin
            if (reset) begin
               rx_state <= RESETTING;
            end else begin
               rx_cnt <= rx_cnt + 1;
               if (rx_cnt == PMA_READY_CYCLES - 1) begin
                  rx_pma_ready       <= 1'b1;
                  rx_is_lockedtodata <= 1'b1;
               end
               if (rx_cnt == READY_CYCLES - 1) begin
                  rx_ready <= 1'b1;
                  rx_state <= READY_ST;
               end
            end
         end

         READY_ST: begin
            if (reset) begin
               rx_state           <= RESETTING;
               rx_ready           <= 1'b0;
               rx_pma_ready       <= 1'b0;
               rx_is_lockedtodata <= 1'b0;
               rx_cnt             <= 0;
            end
         end

         default: rx_state <= RESETTING;
      endcase
   end

   // ----------------------------------------------------------------
   // Data path
   // ----------------------------------------------------------------
   assign sim_tx_parallel_data_o = tx_parallel_data;
   assign rx_parallel_data       = sim_rx_parallel_data_i;

   // Serial outputs: tied to constants (not used in simulation)
   assign tx_serial_data         = 1'b0;
   assign tx_serial_data_n       = 1'b1;

endmodule  // qeciphy_etile_sim_model
