// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// Multi-Channel Pipelined CRC Compute Engine
//------------------------------------------------------------------------------
// This module implements a pipelined CRC computation system that
// calculates multiple CRC values concurrently with staggered timing.
//
// Architecture:
// - Three CRC16-IBM3740 calculators (crc01, crc23, crc45) for data packets
// - One CRC8-SMBUS calculator (crcvw) for validation packets
// - Pipelined enable system for staggered operation
// - Individual reset control for each CRC calculator
//
// Operation:
// - Boundary detection triggers pipeline restart
// - Enable pipeline creates staggered enable signals for CRC calculators
// - Reset pipeline provides individual reset timing for each calculator
//
// Timing:
// - See detailed waveform diagram below for timing relationships
//------------------------------------------------------------------------------

module qeciphy_crc_compute (
    input  logic        clk_i,
    input  logic        rst_n_i,
    input  logic        faw_boundary_i,
    input  logic        crc_boundary_i,
    input  logic [63:0] tdata_i,
    output logic [15:0] crc01_o,
    output logic [15:0] crc23_o,
    output logic [15:0] crc45_o,
    output logic [ 7:0] crcvw_o,
    output logic        crc_valid_o
);

   localparam CRC01_ENABLE_BIT = 1;
   localparam CRC23_ENABLE_BIT = 3;
   localparam CRC45_ENABLE_BIT = 5;

   localparam CRC01_RESET_BIT = 4;
   localparam CRC23_RESET_BIT = 6;
   localparam CRC45_RESET_BIT = 1;
   localparam CRCVW_RESET_BIT = 1;

   //                     +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+   
   // clk_i               |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |   
   //                  ---+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +--+  +---
   //
   //                     +-----+                                   +-----+      
   // crc_boundary_i      |     |                                   |     |      
   //                  ---+     +-----------------------------------+     +------
   //                                                                            
   //                  ---------------------------------+     +------------------
   // crc01_rst_n                                       |     |                  
   //                                                   +-----+                  
   //                                                                            
   //                           +-----------+                             +------
   // crc01_en                  |           |                             |      
   //                  ---------+           +-----------------------------+      
   //                                                                            
   //                                       +-----------+                        
   // crc01_valid                           |           |                        
   //                  ---------------------+           +------------------------
   //                                                                            
   //                  ---+     +-----------------------------------+     +------
   // crc23_rst_n         |     |                                   |     |      
   //                     +-----+                                   +-----+      
   //                                                                            
   //                                       +-----------+                        
   // crc23_en                              |           |                        
   //                  ---------------------+           +------------------------
   //                                                                            
   //                  ---+                             +-----------+            
   // crc23_valid         |                             |           |            
   //                     +-----------------------------+           +------------
   //                                                                            
   //                  ---------------+     +------------------------------------
   // crc45_rst_n                     |     |                                    
   //                                 +-----+                                    
   //                                                                            
   //                  ---+                             +-----------+            
   // crc45_en            |                             |           |            
   //                     +-----------------------------+           +------------
   //                                                                            
   //                     +-----------+                             +------------
   // crc45_valid         |           |                             |            
   //                  ---+           +-----------------------------+            
   //                                                                            
   //                  ---------------+     +------------------------------------
   // crcvw_rst_n                     |     |                                    
   //                                 +-----+                                    
   //                                                                            
   //                     +-----+                                   +-----+      
   // crcvw_en            |     |                                   |     |      
   //                  ---+     +-----------------------------------+     +------
   //                                                                            
   //                           +-----+                                   +------
   // crcvw_valid               |     |                                   |      
   //                  ---------+     +-----------------------------------+      
   //                                                                                                            

   // Pipeline control signals
   logic [ 5:0] enable_pipe;  // Enable pipeline shift register
   logic [ 5:0] enable_pipe_nxt;  // Next value for enable pipeline

   logic [ 6:0] rst_pipe;  // Reset pipeline shift register
   logic [ 6:0] rst_pipe_nxt;  // Next value for reset pipeline

   // CRC enable signals (to CRC modules)
   logic        crc01_en;
   logic        crc23_en;
   logic        crc45_en;
   logic        crcvw_en;

   // CRC valid output signals (from CRC modules)
   logic        crc01_valid;
   logic        crc23_valid;
   logic        crc45_valid;
   logic        crcvw_valid;

   // CRC reset signals (to CRC modules)
   logic        crc01_rst_n;
   logic        crc23_rst_n;
   logic        crc45_rst_n;
   logic        crcvw_rst_n;

   // CRC16 registered results (for output stability)
   logic [15:0] crc01_reg;
   logic [15:0] crc23_reg;

   // CRC calculated values (from CRC modules)
   logic [15:0] crc01_calc;
   logic [15:0] crc23_calc;
   logic [15:0] crc45_calc;
   logic [ 7:0] crcvw_calc;

   logic        boundary_detected;  // Combined boundary detection


   assign boundary_detected = faw_boundary_i || crc_boundary_i;

   // CRC enable generation
   assign crc01_en = enable_pipe[CRC01_ENABLE_BIT] && ~boundary_detected;
   assign crc23_en = enable_pipe[CRC23_ENABLE_BIT] && ~boundary_detected;
   assign crc45_en = enable_pipe[CRC45_ENABLE_BIT] && ~boundary_detected;
   assign crcvw_en = crc_boundary_i;

   // Enable pipeline
   assign enable_pipe_nxt = boundary_detected ? 6'h3 : (enable_pipe << 1);

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) enable_pipe <= '0;
      else enable_pipe <= enable_pipe_nxt;
   end

   // Reset signal generation
   assign crc01_rst_n  = ~rst_pipe[CRC01_RESET_BIT];
   assign crc23_rst_n  = ~rst_pipe[CRC23_RESET_BIT];
   assign crc45_rst_n  = ~rst_pipe[CRC45_RESET_BIT];
   assign crcvw_rst_n  = ~rst_pipe[CRCVW_RESET_BIT];

   // Reset pipeline
   assign rst_pipe_nxt = boundary_detected ? 7'b0000001 : (rst_pipe << 1);

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         rst_pipe <= '0;
      end else begin
         rst_pipe <= rst_pipe_nxt;
      end
   end

   // Output assignments
   assign crc_valid_o = crcvw_valid;  // Overall valid follows CRC8 validation
   assign crc01_o     = crc01_reg;  // CRC16 outputs from registered values
   assign crc23_o     = crc23_reg;
   assign crc45_o     = crc45_calc;
   assign crcvw_o     = crcvw_calc;  // CRC8 output directly from calculator


   // CRC16 result registers: capture calculated values when valid
   // Initialize to 0xFFFF (CRC16-IBM3740 seed value)
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc01_reg <= 16'hFFFF;
      end else if (crc01_valid) begin
         crc01_reg <= crc01_calc;
      end
   end

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc23_reg <= 16'hFFFF;
      end else if (crc23_valid) begin
         crc23_reg <= crc23_calc;
      end
   end

   // CRC Calculator Instantiations
   // Three CRC16-IBM3740 calculators for data packet pairs
   qeciphy_crc16_ibm3740 i_crc01 (
       .clk_i      (clk_i),
       .rst_n_i    (crc01_rst_n),
       .tdata_i    (tdata_i),
       .tvalid_i   (crc01_en),
       .crc_o      (crc01_calc),
       .crc_valid_o(crc01_valid)
   );

   qeciphy_crc16_ibm3740 i_crc23 (
       .clk_i      (clk_i),
       .rst_n_i    (crc23_rst_n),
       .tdata_i    (tdata_i),
       .tvalid_i   (crc23_en),
       .crc_o      (crc23_calc),
       .crc_valid_o(crc23_valid)
   );

   qeciphy_crc16_ibm3740 i_crc45 (
       .clk_i      (clk_i),
       .rst_n_i    (crc45_rst_n),
       .tdata_i    (tdata_i),
       .tvalid_i   (crc45_en),
       .crc_o      (crc45_calc),
       .crc_valid_o(crc45_valid)
   );

   // CRC8-SMBUS calculator for validation packets
   qeciphy_crc8_smbus i_crcvw (
       .clk_i      (clk_i),
       .rst_n_i    (crcvw_rst_n),
       .tdata_i    (tdata_i[15:8]),
       .tvalid_i   (crcvw_en),
       .crc_o      (crcvw_calc),
       .crc_valid_o(crcvw_valid)
   );

endmodule
