// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Evan Sun

//------------------------------------------------------------------------------
// QECIPHY Altera GT Wrapper
//------------------------------------------------------------------------------
// Wraps Intel Agilex F-Tile or E-Tile transceiver IP with soft PCS (8b10b
// encode/decode + word alignment) and soft comma detection to present the same
// interface as qeciphy_gt_xilinx to qeciphy_gt_wrapper.
//
// Tile selection is controlled by GT_TYPE parameter:
//   "FTILE" - Intel Agilex 7 F-Tile (qeciphy_ftile)
//   "ETILE" - Intel Agilex E-Tile  (qeciphy_etile)
//
// Data flow (both tiles):
//   TX: tx_tdata_i (32b) + tx_tdata_charisk_i → [8b10b enc x4] → [Tile IP]
//   RX: [Tile IP] → [word align] → [8b10b dec x4] → [rx_comma_detect] → rx_tdata_o
//
// Clock mapping:
//   tx_clkout2 (2x raw) → qeciphy_altera_clk_mmcm → tx_clk_2x_o (2x), tx_clk_o (1x)
//   rx_clkout2 (2x raw) → qeciphy_altera_clk_mmcm → rx_clk_2x_o (2x), rx_clk_o (1x)
//------------------------------------------------------------------------------
// Note: FTILE support is currently included for completeness but UNTESTED.

module qeciphy_gt_altera #(
    parameter string GT_TYPE = "ETILE"  // Valid values: "ETILE", "FTILE"
) (
    input logic gt_ref_clk_i,

    // GT differential signals
    input  logic gt_rx_p_i,
    input  logic gt_rx_n_i,
    output logic gt_tx_p_o,
    output logic gt_tx_n_o,

    input  logic f_clk_i,
    input  logic gt_rst_n_i,
    output logic gt_power_good_o,

    output logic        tx_clk_o,
    output logic        tx_clk_2x_o,
    input  logic [31:0] tx_tdata_i,
    input  logic [ 3:0] tx_tdata_charisk_i,
    output logic        gt_tx_rst_done_o,

    output logic        rx_clk_o,
    output logic        rx_clk_2x_o,
    output logic [31:0] rx_tdata_o,
    output logic        gt_rx_rst_done_o,
    output logic        rx_byte_aligned_o
);

   // -------------------------------------------------------------
   // Signal declarations
   // -------------------------------------------------------------

   logic        rst;

   // TX path signals
   logic        tx_clkout2;  // 2x raw clock from FTile TX PLL
   logic        tx_reset_sync;  // Reset synchronized to TX 2x clock
   logic [ 4:0] tx_reset_sync_ff;
   logic        rx_reset_sync;
   logic [ 4:0] rx_reset_sync_ff;
   logic        tx_reset_ack;
   logic        tx_ready;
   logic        tx_reset_phy;
   logic        tx_pll_locked;
   logic [39:0] tx_encoded;
   logic [79:0] tx_parallel_data;

   // TX ready synchronizer to tx_clk_2x_o domain
   logic [ 4:0] tx_ready_2x_sync_ff;
   logic        tx_ready_2x_sync;

   // TX ready synchronizer to f_clk_i domain
   logic [ 4:0] tx_ready_sync_ff;
   logic        tx_ready_sync;

   // RX path signals
   logic        rx_clkout2;  // 2x raw clock from FTile RX CDR
   logic        rx_reset_ack;
   logic        rx_ready;
   logic        rx_reset_phy;
   logic        rx_freqlocked;
   logic        rx_is_locked_to_ref;
   logic [79:0] rx_parallel_data;

   // E-Tile-specific signals (unused in FTILE path)
   logic [39:0] rx_unaligned;
   logic [39:0] word_aligner_data_out;

   // Datapath reset signals
   logic        tx_reset_datapath;
   logic        rx_reset_datapath;

   // RX ready synchronizer to rx_clk_2x_o domain
   logic [ 4:0] rx_ready_2x_sync_ff;
   logic        rx_ready_2x_sync;

   // RX ready synchronizer to f_clk_i domain
   logic [ 4:0] rx_ready_sync_ff;
   logic        rx_ready_sync;

   // Comma detection signals
   logic        rx_byte_aligned;
   logic        word_align_done;
   logic        word_align_fail;

   // GT Reset counter
   logic [ 8:0] gt_power_reset_counter = 9'b0;

`ifdef TILE_SIM_MODEL
   // Sim-only cross-connect signals accessed hierarchically by the testbench.
   // sim_tile_tx_parallel_data: exposes this instance's TX to the peer's RX.
   // sim_tile_rx_parallel_data: receives the peer's TX (driven by testbench).
   logic [79:0] sim_tile_tx_parallel_data;
   logic [79:0] sim_tile_rx_parallel_data;
`endif


   // -------------------------------------------------------------
   // Derived resets
   // -------------------------------------------------------------

   assign rst             = ~gt_rst_n_i;
   // F-Tile does not have a power-good signal; tie high.
   assign gt_power_good_o = (gt_power_reset_counter == '1);

   always_ff @(posedge f_clk_i) begin
      if (gt_power_reset_counter != '1) begin
         gt_power_reset_counter <= gt_power_reset_counter + 1;
      end
   end


   // -------------------------------------------------------------
   // Output assignments
   // -------------------------------------------------------------

   assign rx_byte_aligned_o = rx_byte_aligned;
   assign gt_tx_rst_done_o  = tx_ready_sync;
   assign gt_rx_rst_done_o  = rx_ready_sync;

   // -------------------------------------------------------------
   // TX reset synchronization to tx_clk_2x_o domain
   // -------------------------------------------------------------


   always_ff @(posedge tx_clk_2x_o) begin
      tx_reset_sync_ff <= {tx_reset_sync_ff[3:0], rst};
      tx_reset_sync    <= tx_reset_sync_ff[4];
   end

   always_ff @(posedge rx_clk_2x_o) begin
      rx_reset_sync_ff <= {rx_reset_sync_ff[3:0], rst};
      rx_reset_sync    <= rx_reset_sync_ff[4];
   end


   // -------------------------------------------------------------
   // TX / RX ready synchronization to 2x clock domains
   // -------------------------------------------------------------

   always_ff @(posedge tx_clk_2x_o) begin
      tx_ready_2x_sync_ff <= {tx_ready_2x_sync_ff[3:0], tx_ready};
      tx_ready_2x_sync    <= tx_ready_2x_sync_ff[4];
   end

   always_ff @(posedge rx_clk_2x_o) begin
      rx_ready_2x_sync_ff <= {rx_ready_2x_sync_ff[3:0], rx_ready};
      rx_ready_2x_sync    <= rx_ready_2x_sync_ff[4];
   end

   // -------------------------------------------------------------
   // TX / RX ready synchronization to f_clk_i domain
   // -------------------------------------------------------------

   always_ff @(posedge f_clk_i) begin
      tx_ready_sync_ff <= {tx_ready_sync_ff[3:0], tx_ready};
      tx_ready_sync    <= tx_ready_sync_ff[4];
   end

   always_ff @(posedge f_clk_i) begin
      rx_ready_sync_ff <= {rx_ready_sync_ff[3:0], rx_ready};
      rx_ready_sync    <= rx_ready_sync_ff[4];
   end

   // -------------------------------------------------------------
   // RX ready synchronization to rx_clk_2x_o domain
   // -------------------------------------------------------------
   // RX datapath reset: hold in reset until FTile RX is ready, or when
   // comma detect or word aligner requests a datapath reset (alignment retry).

   // RX datapath reset: hold in reset until FTile RX is ready, or when
   // comma detect or word aligner requests a datapath reset (alignment retry).

   assign tx_reset_datapath = (tx_reset_sync || !tx_ready_2x_sync) ? 1'b1 : 1'b0;
   assign rx_reset_datapath = (rx_reset_sync || !rx_ready_2x_sync || word_align_fail) ? 1'b1 : 1'b0;



   // -------------------------------------------------------------
   // TX data path: 8b10b encoding (x4, 32-bit wide)
   // -------------------------------------------------------------
   // Format TX parallel data for F-Tile 80-bit interface:
   //   [79]    = fifo_wr_en (write enable)
   //   [78:60] = reserved
   //   [59:40] = tx_encoded[39:20] (upper 20 bits of 40-bit encoded stream)
   //   [39]    = reserved
   //   [38]    = data_valid
   //   [37:20] = reserved
   //   [19:0]  = tx_encoded[19:0]  (lower 20 bits of 40-bit encoded stream)

   eth_8b10b_enc_x4_a u_8b10b_encoder_4x (
       .clk     (tx_clk_2x_o),
       .sclr    (tx_reset_datapath),
       .din_k   (tx_tdata_charisk_i),
       .din_dat (tx_tdata_i),
       .dout_dat(tx_encoded)
   );

   assign tx_parallel_data = {
      1'b1,  // [79] Write enable for elastic FIFO
      19'b0,  // [78:60] Reserved
      tx_encoded[39:20],  // [59:40] Upper 20 bits of encoded data
      1'b0,  // [39] Reserved
      1'b1,  // [38] Data valid
      18'b0,  // [37:20] Reserved
      tx_encoded[19:0]  // [19:0] Lower 20 bits of encoded data
   };

   // -------------------------------------------------------------
   // RX data path: word alignment then 8b10b decoding (x4)
   // -------------------------------------------------------------

   // Concatenate FTile 80-bit parallel data to 40-bit word for aligner
   assign rx_unaligned = {rx_parallel_data[59:40], rx_parallel_data[19:0]};

   // Word aligner: barrel-shifts raw 40-bit stream and automatically
   // detects K28.5 comma patterns in the encoded output to align.
   qeciphy_word_align #(
       .DATA_WIDTH        (40),
       .WORD_SIZE         (10),
       .TX_PATTERN_LENGTH (128),
       .RXSLIDE_COUNT_MAX (80),
       .RX_ALIGN_MATCH_MAX(8)
   ) u_word_aligner (
       .clk         (rx_clk_2x_o),
       .rst_n_i     (~rx_reset_datapath),
       .rx_datain   (rx_unaligned),
       .rx_dataout  (word_aligner_data_out),
       .o_align_done(word_align_done),
       .o_align_fail(word_align_fail)
   );

   eth_8b10b_dec_x4_a u_8b10b_decoder_4x (
       .clk       (rx_clk_2x_o),
       .sclr      (rx_reset_datapath),
       .din_dat   (word_aligner_data_out),
       .dout_dat  (rx_tdata_o),
       .dout_k    (),
       .dout_kerr (),
       .dout_rderr(),
       .dout_rdreg()
   );

   // -------------------------------------------------------------
   // Soft comma detection (replaces Xilinx GT hardware comma assist)
   // -------------------------------------------------------------
   // comma_realign_i is tied to 0: the word aligner handles byte-level
   // realignment internally; the comma detect monitors the data stream
   // and asserts rx_byte_aligned once a stable QECIPHY comma pattern
   // is observed.

   qeciphy_rx_comma_detect #(
       .TX_PATTERN_LENGTH(128),
       .MAX_REVIEWS      (128),
       .MAX_RETRIES      (32)
   ) i_qeciphy_rx_comma_detect (
       .clk_i               (rx_clk_2x_o),
       .rst_n_i             (~rx_reset_datapath && word_align_done),
       .comma_realign_i     (1'b0),
       .tdata_i             (rx_tdata_o),
       .align_done_o        (rx_byte_aligned),
       .rx_datapath_resetn_o()
   );

   // -------------------------------------------------------------
   // Clock generation via Altera PLL dividers
   // -------------------------------------------------------------
   // FTile outputs 2x (257.8125 MHz) clocks on tx_clkout2 / rx_clkout2.
   // qeciphy_altera_clk_mmcm divides to provide both 2x (clock_div1x)
   // and 1x (clock_div2x) clocks.

   qeciphy_altera_clk_mmcm tile_tx_clk_network (
       .inclk      (tx_clkout2),   // 257.8125 MHz input from FTile TX PLL
       .clock_div1x(tx_clk_2x_o),  // 257.8125 MHz output (2x clock for 32-bit path)
       .clock_div2x(tx_clk_o)      // 128.90625 MHz output (1x clock for 64-bit path)
   );

   qeciphy_altera_clk_mmcm tile_rx_clk_network (
       .inclk      (rx_clkout2),   // 257.8125 MHz input from FTile RX CDR
       .clock_div1x(rx_clk_2x_o),  // 257.8125 MHz output (2x clock for 32-bit path)
       .clock_div2x(rx_clk_o)      // 128.90625 MHz output (1x clock for 64-bit path)
   );

   // -------------------------------------------------------------
   // Transceiver instantiation: E-Tile or F-Tile
   // -------------------------------------------------------------

   generate
      if (GT_TYPE == "ETILE") begin : gen_etile

         assign tx_reset_ack = '0;
         assign rx_reset_ack = '0;

`ifdef TILE_SIM_MODEL
         qeciphy_etile_sim_model transceiver_inst (
             .pll_refclk0 (gt_ref_clk_i),
             .reset       (rst),
             .tx_coreclkin(tx_clk_2x_o),
             .rx_coreclkin(rx_clk_2x_o),
             .tx_ready    (tx_ready),
             .rx_ready    (rx_ready),

             .tx_clkout             (),
             .tx_clkout2            (tx_clkout2),
             .rx_clkout             (),
             .rx_clkout2            (rx_clkout2),
             .tx_serial_data        (gt_tx_p_o),
             .tx_serial_data_n      (gt_tx_n_o),
             .rx_serial_data        (gt_rx_p_i),
             .rx_serial_data_n      (gt_rx_n_i),
             .rx_is_lockedtodata    (rx_freqlocked),
             .tx_parallel_data      (tx_parallel_data),
             .rx_parallel_data      (rx_parallel_data),
             .sim_tx_parallel_data_o(sim_tile_tx_parallel_data),
             .sim_rx_parallel_data_i(sim_tile_rx_parallel_data)
         );
`else
         qeciphy_etile transceiver_inst (
             .reset             (rst),
             .pll_refclk0       (gt_ref_clk_i),
             .tx_coreclkin      (tx_clk_2x_o),
             .rx_coreclkin      (rx_clk_2x_o),
             .tx_ready          (tx_ready),
             .rx_ready          (rx_ready),
             .tx_pma_ready      (tx_pma_ready),
             .rx_pma_ready      (rx_pma_ready),
             .tx_clkout         (),
             .tx_clkout2        (tx_clkout2),
             .rx_clkout         (),
             .rx_clkout2        (rx_clkout2),
             .tx_serial_data    (gt_tx_p_o),
             .tx_serial_data_n  (gt_tx_n_o),
             .rx_serial_data    (gt_rx_p_i),
             .rx_serial_data_n  (gt_rx_n_i),
             .rx_is_lockedtodata(rx_freqlocked),
             .tx_parallel_data  (tx_parallel_data),
             .rx_parallel_data  (rx_parallel_data)
         );
`endif

      end else begin : gen_ftile

         assign tx_reset_phy = rst;
         assign rx_reset_phy = rst;
`ifdef TILE_SIM_MODEL
         qeciphy_ftile_sim_model transceiver_inst (
             .rx_cdr_refclk_link    (gt_ref_clk_i),
             .tx_pll_refclk_link    (gt_ref_clk_i),
             .tx_reset              (tx_reset_phy),
             .rx_reset              (rx_reset_phy),
             .tx_reset_ack          (tx_reset_ack),
             .rx_reset_ack          (rx_reset_ack),
             .tx_ready              (tx_ready),
             .rx_ready              (rx_ready),
             .tx_coreclkin          (tx_clk_2x_o),
             .rx_coreclkin          (rx_clk_2x_o),
             .tx_clkout             (),
             .tx_clkout2            (tx_clkout2),
             .rx_clkout             (),
             .rx_clkout2            (rx_clkout2),
             .tx_serial_data        (gt_tx_p_o),
             .tx_serial_data_n      (gt_tx_n_o),
             .rx_serial_data        (gt_rx_p_i),
             .rx_serial_data_n      (gt_rx_n_i),
             .tx_pll_locked         (tx_pll_locked),
             .rx_is_lockedtodata    (rx_freqlocked),
             .rx_is_lockedtoref     (rx_is_locked_to_ref),
             .tx_fifo_full          (),
             .tx_fifo_empty         (),
             .tx_pmaif_fifo_empty   (),
             .tx_pmaif_fifo_pempty  (),
             .tx_pmaif_fifo_pfull   (),
             .tx_parallel_data      (tx_parallel_data),
             .rx_parallel_data      (rx_parallel_data),
             .sim_tx_parallel_data_o(sim_tile_tx_parallel_data),
             .sim_rx_parallel_data_i(sim_tile_rx_parallel_data)
         );
`else
         qeciphy_ftile transceiver_inst (
             .rx_cdr_refclk_link  (gt_ref_clk_i),         // RX CDR reference clock
             .tx_pll_refclk_link  (gt_ref_clk_i),         // TX PLL reference clock
             .tx_reset            (tx_reset_phy),         // TX reset (active-high)
             .rx_reset            (rx_reset_phy),         // RX reset (active-high)
             .tx_reset_ack        (tx_reset_ack),
             .rx_reset_ack        (rx_reset_ack),
             .tx_ready            (tx_ready),             // TX datapath ready
             .rx_ready            (rx_ready),             // RX datapath ready
             .tx_coreclkin        (tx_clk_2x_o),          // TX core clock input (2x)
             .rx_coreclkin        (rx_clk_2x_o),          // RX core clock input (2x)
             .tx_clkout           (),
             .tx_clkout2          (tx_clkout2),           // TX 2x raw clock output
             .rx_clkout           (),
             .rx_clkout2          (rx_clkout2),           // RX 2x raw clock output
             .tx_serial_data      (gt_tx_p_o),            // TX serial positive
             .tx_serial_data_n    (gt_tx_n_o),            // TX serial negative
             .rx_serial_data      (gt_rx_p_i),            // RX serial positive
             .rx_serial_data_n    (gt_rx_n_i),            // RX serial negative
             .tx_pll_locked       (tx_pll_locked),
             .rx_is_lockedtodata  (rx_freqlocked),
             .rx_is_lockedtoref   (rx_is_locked_to_ref),
             .tx_fifo_full        (),
             .tx_fifo_empty       (),
             .tx_pmaif_fifo_empty (),
             .tx_pmaif_fifo_pempty(),
             .tx_pmaif_fifo_pfull (),
             .tx_parallel_data    (tx_parallel_data),     // 80-bit TX data to FTile
             .rx_parallel_data    (rx_parallel_data)      // 80-bit RX data from FTile
         );
`endif

      end
   endgenerate

endmodule  // qeciphy_gt_altera
