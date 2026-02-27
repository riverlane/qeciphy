// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// TX Packet Generator
//------------------------------------------------------------------------------
// This module implements a 3-stage pipeline for transmit packet generation in
// the QECIPHY, handling Frame Alignment Words (FAW), CRC computation,
// and validation packet insertion.
//
// Operation:
// - Stage 0: Multiplexes between Frame Alignment Words, Validation Words, user data, and idle words
// - Stage 1: Simple delay stage allowing CRC computation on stage 0 data
// - Stage 2: Inserts computed CRC values into validation words or passes data through
// - Tracks valid data segments using a circular pointer and bitmask
// - Supports transmission states: active (boundary chars + user data / idle words), 
//   idle (boundary chars + idle words), off (idle words)
//
// Pipeline Flow:
// Input -> Stage 0 (Data MUX) -> Stage 1 (Delay) -> Stage 2 (CRC Insert) -> Output
//
// Control Signals:
// - tx_active_i: Enables user data transmission
// - tx_idle_i: Allows boundary character insertion
// - tx_off_i: Forces idle word transmission
//------------------------------------------------------------------------------

`include "qeciphy_pkg.sv"

module qeciphy_tx_packet_gen (
    input  logic        clk_i,                 // Clock input
    input  logic        rst_n_i,               // Active-low reset
    input  logic        faw_boundary_i,        // FAW boundary
    input  logic        crc_boundary_i,        // CRC boundary
    input  logic [63:0] s_axis_tdata_i,        // Input user data stream
    input  logic        s_axis_tvalid_i,       // Input data valid signal
    output logic        s_axis_tready_o,       // Ready to accept input data
    output logic [63:0] m_axis_tdata_o,        // Output data stream
    output logic        m_axis_tdata_isfaw_o,  // Output indicates if m_axis_tdata is FAW
    input  logic        tx_off_i,              // Transmission off (forces idle words)
    input  logic        tx_idle_i,             // Transmission idle state
    input  logic        tx_active_i,           // Transmission active state
    input  logic        rx_rdy_i               // Receiver ready status to transmit
);

   // 3-stage data pipeline for packet generation
   logic                         [63:0] tdata_pipe                                                                      [0:2];  // Pipeline data registers [stage0, stage1, stage2]
   logic                         [63:0] tdata_pipe_nxt                                                                  [0:2];  // Next values for pipeline data

   // 3 stage pipeline to track if data is FAW
   logic                                tdata_isfaw_pipe                                                                [0:2];

   // Valid bit tracking for data segments  
   logic                         [ 5:0] data_valid_mask;  // Bitmask tracking which data segments contain valid data
   logic                         [ 2:0] valid_bit_ptr;  // Circular pointer to current valid bit position (0-5)
   logic                         [ 2:0] valid_bit_ptr_nxt;  // Next value for valid bit pointer

   // CRC computation results for different data lanes
   logic                         [15:0] crc01_calc;  // CRC result for data words 0-1
   logic                         [15:0] crc23_calc;  // CRC result for data words 2-3  
   logic                         [15:0] crc45_calc;  // CRC result for data words 4-5
   logic                         [ 7:0] crcvw_calc;  // CRC result for valid word field
   logic                                crc_valid;  // CRC computation valid flag from qeciphy_crc_compute module

   // Delayed boundary signals for pipeline synchronization
   logic                                faw_boundary_q;  // Registered FAW boundary signal
   logic                                crc_boundary_q;  // Registered CRC boundary signal

   // Control signals for packet generation modes
   logic                                boundary_chars_enable;  // Enable boundary character insertion (FAW/CRC packets)
   logic                         [ 1:0] boundary_chars_enable_pipe;  // 2-stage pipeline of boundary enable signal
   logic                                data_enable;  // Enable user data transmission

   // Packet structure instances
   qeciphy_pkg::qeciphy_faw_t           faw;  // Frame Alignment Word
   qeciphy_pkg::qeciphy_vd_pkt_t        vd_pkt_pipe                                                                     [0:2];  // Validation Word pipeline 
   qeciphy_pkg::qeciphy_vd_pkt_t        vd_pkt_pipe_nxt                                                                 [0:2];  // Next values for validation Word pipeline

   // Ready when active and not inserting boundary characters
   assign s_axis_tready_o = tx_active_i && !faw_boundary_i && !crc_boundary_i;

   // Output from final pipeline stage
   assign m_axis_tdata_o = tdata_pipe[2];

   // Indicate if output data is FAW
   assign m_axis_tdata_isfaw_o = tdata_isfaw_pipe[2];

   // Enable boundary characters during active or idle transmission states
   assign boundary_chars_enable = tx_active_i || tx_idle_i;

   // Enable user data transmission only during active state
   assign data_enable = tx_active_i;

   // Pipeline the boundary enable signal to synchronize with data pipeline
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         boundary_chars_enable_pipe <= 2'd0;
      end else begin
         boundary_chars_enable_pipe <= {boundary_chars_enable_pipe[0], boundary_chars_enable};
      end
   end

   // Build FAW packet with receiver status and alignment patterns
   always_comb begin
      faw.rx_rdy         = rx_rdy_i;
      faw.reserved_62_40 = 23'h0;
      faw.word_comma     = qeciphy_pkg::WORD_ALIGNMENT_COMMA;
      faw.reserved_31_8  = 24'h0;
      faw.byte_comma     = qeciphy_pkg::BYTE_ALIGNMENT_COMMA;
   end

   // Build Validation Word with placeholder CRC values
   always_comb begin
      vd_pkt_pipe_nxt[0].crc45          = 16'h0;
      vd_pkt_pipe_nxt[0].crc23          = 16'h0;
      vd_pkt_pipe_nxt[0].crc01          = 16'h0;
      vd_pkt_pipe_nxt[0].reserved_15_14 = 2'b00;
      vd_pkt_pipe_nxt[0].valids         = data_valid_mask;
      vd_pkt_pipe_nxt[0].crcvw          = 8'h0;
   end

   // Pipeline Stage 0 - Data multiplexing
   // Select data source based on boundary signals and transmission state
   assign tdata_pipe_nxt[0] = boundary_chars_enable ? 
                               (faw_boundary_i ? faw : 
                               (crc_boundary_i ? vd_pkt_pipe_nxt[0] : 
                               (data_enable ? (s_axis_tvalid_i ? s_axis_tdata_i : qeciphy_pkg::IDLE_WORD) : qeciphy_pkg::IDLE_WORD))) 
                               : qeciphy_pkg::IDLE_WORD;

   // Register stage 0 data
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         tdata_pipe[0] <= 64'd0;
      end else begin
         tdata_pipe[0] <= tdata_pipe_nxt[0];
      end
   end

   // Pipeline Stage 1 - Delay for CRC computation
   // Register stage 1 data
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         tdata_pipe[1] <= 64'd0;
      end else begin
         tdata_pipe[1] <= tdata_pipe[0];
      end
   end

   // Extract validation packet structure from stage 1
   assign vd_pkt_pipe[1] = qeciphy_pkg::qeciphy_vd_pkt_t'(tdata_pipe[1]);

   // Build complete validation packet with computed CRC values
   always_comb begin
      vd_pkt_pipe_nxt[2].crc45          = crc45_calc;
      vd_pkt_pipe_nxt[2].crc23          = crc23_calc;
      vd_pkt_pipe_nxt[2].crc01          = crc01_calc;
      vd_pkt_pipe_nxt[2].reserved_15_14 = 2'b00;
      vd_pkt_pipe_nxt[2].valids         = vd_pkt_pipe[1].valids;  // Preserve valid bits from previous stage
      vd_pkt_pipe_nxt[2].crcvw          = crcvw_calc;
   end

   // Pipeline Stage 2 - CRC insertion
   // Insert CRC-updated validation word in the correct position
   assign tdata_pipe_nxt[2] = boundary_chars_enable_pipe[1] && crc_valid ? vd_pkt_pipe_nxt[2] : tdata_pipe[1];

   // Register final output stage
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         tdata_pipe[2] <= 64'd0;
      end else begin
         tdata_pipe[2] <= tdata_pipe_nxt[2];
      end
   end

   // Track if current data is FAW through the pipeline
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         tdata_isfaw_pipe[0] <= 1'b0;
      end else begin
         tdata_isfaw_pipe[0] <= boundary_chars_enable && faw_boundary_i;
      end
   end

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         tdata_isfaw_pipe[1] <= 1'b0;
         tdata_isfaw_pipe[2] <= 1'b0;
      end else begin
         tdata_isfaw_pipe[1] <= tdata_isfaw_pipe[0];
         tdata_isfaw_pipe[2] <= tdata_isfaw_pipe[1];
      end
   end

   // Reset pointer on boundary insertion, otherwise increment circularly (0-5)
   assign valid_bit_ptr_nxt = (faw_boundary_i || crc_boundary_i) ? 3'd0 : (valid_bit_ptr + 3'd1);

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         valid_bit_ptr <= 3'd0;
      end else begin
         valid_bit_ptr <= valid_bit_ptr_nxt;
      end
   end

   // Track which data segments contain valid information using bitmask
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         data_valid_mask <= 6'd0;
      end else begin
         data_valid_mask[valid_bit_ptr] <= s_axis_tvalid_i && s_axis_tready_o;
      end
   end

   // Delay FAW boundary signal for CRC computation timing synchronization
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_boundary_q <= 1'b0;
      end else begin
         faw_boundary_q <= faw_boundary_i;
      end
   end

   // Delay CRC boundary signal for CRC computation timing synchronization  
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_boundary_q <= 1'b0;
      end else begin
         crc_boundary_q <= crc_boundary_i;
      end
   end

   // Instantiate CRC computation module
   qeciphy_crc_compute i_crc_compute (
       .clk_i         (clk_i),           // Clock input
       .rst_n_i       (rst_n_i),         // Active-low reset  
       .faw_boundary_i(faw_boundary_q),  // Delayed FAW boundary for sync
       .crc_boundary_i(crc_boundary_q),  // Delayed CRC boundary for sync
       .tdata_i       (tdata_pipe[0]),   // Data input from pipeline stage 0
       .crc01_o       (crc01_calc),      // CRC result for data words 0-1
       .crc23_o       (crc23_calc),      // CRC result for data words 2-3
       .crc45_o       (crc45_calc),      // CRC result for data words 4-5
       .crcvw_o       (crcvw_calc),      // CRC result for valid word field
       .crc_valid_o   (crc_valid)        // CRC computation valid flag
   );

endmodule  // qeciphy_tx_packet_gen
