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
   // Local parameters
   // -------------------------------------------------------------

   // 8b10b codec parameters
   localparam DATA_WIDTH = 40;   // Encoded data width (4 symbols × 10 bits)
   localparam WORD_SIZE  = 10;   // 8b10b symbol size

   // Word alignment parameters
   localparam TX_PATTERN_LENGTH  = 128;  // Cycles to wait for comma pattern
   localparam RXSLIDE_COUNT_MAX  = 80;   // Max bit positions to try
   localparam RX_ALIGN_MATCH_MAX = 8;    // Required consecutive matches

   // Comma detection parameters
   localparam MAX_REVIEWS = 128;  // Reviews before declaring aligned
   localparam MAX_RETRIES = 32;   // Retries before failure

   // -------------------------------------------------------------
   // Signal declarations
   // -------------------------------------------------------------

   // Tile parallel data struct for 80-bit interface
   // Format for F-Tile/E-Tile 80-bit parallel interface:
   //   [79]    = fifo_wr_en (write enable for elastic FIFO)
   //   [78:60] = reserved
   //   [59:40] = data_hi (upper 20 bits of 40-bit encoded stream)
   //   [39]    = reserved
   //   [38]    = data_valid
   //   [37:20] = reserved
   //   [19:0]  = data_lo (lower 20 bits of 40-bit encoded stream)
   typedef struct packed {
      logic        fifo_wr_en;   // [79]
      logic [18:0] reserved_hi;  // [78:60]
      logic [19:0] data_hi;      // [59:40]
      logic        reserved_mid; // [39]
      logic        data_valid;   // [38]
      logic [17:0] reserved_lo;  // [37:20]
      logic [19:0] data_lo;      // [19:0]
   } tile_parallel_data_t;

   logic        rst;

   // TX path signals
   logic                  tx_clkout2;  // 2x raw clock from FTile TX PLL
   logic                  tx_reset_sync;  // Reset synchronized to TX 2x clock
   logic                  rx_reset_sync;  // Reset synchronized to RX 2x clock
   logic                  tx_reset_sync_n;  // Reset synchronized to TX 2x clock
   logic                  rx_reset_sync_n;  // Reset synchronized to RX 2x clock
   logic                  tx_reset_ack;
   logic                  tx_ready;
   logic                  tx_pll_locked;
   logic [39:0]           tx_encoded;
   tile_parallel_data_t   tx_parallel_data;

   // TX ready synchronizer to tx_clk_2x_o domain
   logic        tx_ready_2x_sync;

   // TX ready synchronizer to f_clk_i domain
   logic        tx_ready_sync;

   // RX path signals
   logic                  rx_clkout2;  // 2x raw clock from FTile RX CDR
   logic                  rx_reset_ack;
   logic                  rx_ready;
   logic                  rx_freqlocked;
   logic                  rx_is_locked_to_ref;
   tile_parallel_data_t   rx_parallel_data;

   // E-Tile-specific signals (unused in FTILE path)
   logic [39:0] rx_unaligned;
   logic [39:0] word_aligner_data_out;

   // Datapath reset signals
   logic        tx_reset_datapath;
   logic        rx_reset_datapath;

   // RX ready synchronizer to rx_clk_2x_o domain
   logic        rx_ready_2x_sync;

   // RX ready synchronizer to f_clk_i domain
   logic        rx_ready_sync;

   // Comma detection signals
   logic        rx_byte_aligned;
   logic        word_align_done;
   logic        word_align_fail;

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
   assign gt_power_good_o = 1'b1;


   // -------------------------------------------------------------
   // Output assignments
   // -------------------------------------------------------------

   assign rx_byte_aligned_o = rx_byte_aligned;
   assign gt_tx_rst_done_o  = tx_ready_sync;
   assign gt_rx_rst_done_o  = rx_ready_sync;

   // -------------------------------------------------------------
   // TX/RX reset synchronization using proper reset synchronizers
   // -------------------------------------------------------------
   // Use riv_synchronizer_2ff with ASYNC reset to safely cross
   // the asynchronous reset into the TX/RX clock domains.

   assign tx_reset_sync = ~tx_reset_sync_n;
   assign rx_reset_sync = ~rx_reset_sync_n;
   
   riv_synchronizer_2ff #(
       .RESET_TYPE("ASYNC")
   ) i_tx_reset_sync (
       .src_in   (1'b1),
       .dst_clk  (tx_clk_2x_o),
       .dst_rst_n(gt_rst_n_i),
       .dst_out  (tx_reset_sync_n)
   );

   riv_synchronizer_2ff #(
       .RESET_TYPE("ASYNC")
   ) i_rx_reset_sync (
       .src_in   (1'b1),
       .dst_clk  (rx_clk_2x_o),
       .dst_rst_n(gt_rst_n_i),
       .dst_out  (rx_reset_sync_n)
   );


   // -------------------------------------------------------------
   // TX / RX ready synchronization to 2x clock domains
   // -------------------------------------------------------------

   riv_synchronizer_2ff #(
       .RESET_TYPE("ASYNC")
   )i_tx_ready_2x_sync (
       .src_in   (tx_ready),
       .dst_clk  (tx_clk_2x_o),
       .dst_rst_n(gt_rst_n_i),
       .dst_out  (tx_ready_2x_sync)
   );

   riv_synchronizer_2ff #(
       .RESET_TYPE("ASYNC")
   ) i_rx_ready_2x_sync (
       .src_in   (rx_ready),
       .dst_clk  (rx_clk_2x_o),
       .dst_rst_n(gt_rst_n_i),
       .dst_out  (rx_ready_2x_sync)
   );

   // -------------------------------------------------------------
   // TX / RX ready synchronization to f_clk_i domain
   // -------------------------------------------------------------

   riv_synchronizer_2ff #(
       .RESET_TYPE("ASYNC")
   ) i_tx_ready_sync (
       .src_in   (tx_ready),
       .dst_clk  (f_clk_i),
       .dst_rst_n(gt_rst_n_i),
       .dst_out  (tx_ready_sync)
   );

   riv_synchronizer_2ff #(
       .RESET_TYPE("ASYNC")
   ) i_rx_ready_sync (
       .src_in   (rx_ready),
       .dst_clk  (f_clk_i),
       .dst_rst_n(gt_rst_n_i),
       .dst_out  (rx_ready_sync)
   );

   // -------------------------------------------------------------
   // RX ready synchronization to rx_clk_2x_o domain
   // -------------------------------------------------------------
   // RX datapath reset: hold in reset until FTile RX is ready, or when
   // comma detect or word aligner requests a datapath reset (alignment retry).

   assign tx_reset_datapath = tx_reset_sync || !tx_ready_2x_sync;
   assign rx_reset_datapath = rx_reset_sync || !rx_ready_2x_sync || word_align_fail;



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

   assign tx_parallel_data.fifo_wr_en   = 1'b1;
   assign tx_parallel_data.reserved_hi  = 19'b0;
   assign tx_parallel_data.data_hi      = tx_encoded[39:20];
   assign tx_parallel_data.reserved_mid = 1'b0;
   assign tx_parallel_data.data_valid   = 1'b1;
   assign tx_parallel_data.reserved_lo  = 18'b0;
   assign tx_parallel_data.data_lo      = tx_encoded[19:0];

   // -------------------------------------------------------------
   // RX data path: word alignment then 8b10b decoding (x4)
   // -------------------------------------------------------------

   // Extract 40-bit encoded data from Tile 80-bit parallel interface for aligner
   assign rx_unaligned = {rx_parallel_data.data_hi, rx_parallel_data.data_lo};

   // Word aligner: barrel-shifts raw 40-bit stream and automatically
   // detects K28.5 comma patterns in the encoded output to align.
   qeciphy_word_align #(
       .DATA_WIDTH        (DATA_WIDTH),
       .WORD_SIZE         (WORD_SIZE),
       .TX_PATTERN_LENGTH (TX_PATTERN_LENGTH),
       .RXSLIDE_COUNT_MAX (RXSLIDE_COUNT_MAX),
       .RX_ALIGN_MATCH_MAX(RX_ALIGN_MATCH_MAX)
   ) u_word_aligner (
       .clk_i       (rx_clk_2x_o),
       .rst_n_i     (~rx_reset_datapath),
       .rx_datain_i (rx_unaligned),
       .rx_dataout_o(word_aligner_data_out),
       .align_done_o(word_align_done),
       .align_fail_o(word_align_fail)
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
       .TX_PATTERN_LENGTH(TX_PATTERN_LENGTH),
       .MAX_REVIEWS      (MAX_REVIEWS),
       .MAX_RETRIES      (MAX_RETRIES)
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
   // FTile and ETile output line_rate/data_width (nominally 10.3125 Gbps / 40 bits = 257.8125 MHz) clocks on tx_clkout2 / rx_clkout2.
   // qeciphy_altera_clk_mmcm divides to provide both InClk and divide-by-2 InClk outputs for the 32-bit and 64-bit datapaths, respectively.

   qeciphy_altera_clk_mmcm tile_tx_clk_network (
       .inclk      (tx_clkout2),   // Nominally 257.8125 MHz input from Tile TX PLL
       .clock_div1x(tx_clk_2x_o),  // Inclk output (nominally 257.8125 MHz for 32-bit path)
       .clock_div2x(tx_clk_o)      // Inclk/2 output (nominally 128.90625 MHz for 64-bit path)
   );

   qeciphy_altera_clk_mmcm tile_rx_clk_network (
       .inclk      (rx_clkout2),   // Nominally 257.8125 MHz input from Tile RX CDR
       .clock_div1x(rx_clk_2x_o),  // Inclk output (nominally 257.8125 MHz for 32-bit path)
       .clock_div2x(rx_clk_o)      // Inclk/2 output (nominally 128.90625 MHz for 64-bit path)
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
             .reset       (~gt_rst_n_i),
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
             .reset             (~gt_rst_n_i),
             .pll_refclk0       (gt_ref_clk_i),
             .tx_coreclkin      (tx_clk_2x_o),
             .rx_coreclkin      (rx_clk_2x_o),
             .tx_ready          (tx_ready),
             .rx_ready          (rx_ready),
             .tx_pma_ready      (),
             .rx_pma_ready      (),
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

      end else if (GT_TYPE == "FTILE") begin : gen_ftile

`ifdef TILE_SIM_MODEL
         qeciphy_ftile_sim_model transceiver_inst (
             .rx_cdr_refclk_link    (gt_ref_clk_i),
             .tx_pll_refclk_link    (gt_ref_clk_i),
             .tx_reset              (~gt_rst_n_i),
             .rx_reset              (~gt_rst_n_i),
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
             .tx_reset            (~gt_rst_n_i),         // TX reset (active-high)
             .rx_reset            (~gt_rst_n_i),         // RX reset (active-high)
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
        end else begin : gen_invalid
             initial begin
                $error("Invalid GT_TYPE parameter value: %s. Valid values are 'ETILE' or 'FTILE'.", GT_TYPE);
                $finish;
             end

      end
   endgenerate

endmodule  // qeciphy_gt_altera
