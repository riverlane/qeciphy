// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// TX Boundary Generator
//------------------------------------------------------------------------------
// This module generates timing boundaries for FAW (Frame Alignment Word) and 
// CRC insertion in the transmit path.
//
// Operation:
// - Generates FAW boundaries every 64 clock cycles (faw_boundary_o)
// - Provides early warning signal one cycle before FAW (almost_faw_boundary_o)
// - Generates CRC boundaries every 7 clock cycles for CRC insertion timing
// - CRC boundaries are disabled until after the first FAW boundary
// - All counters run continuously once started
// - No enable/disable functionality (always active when not in reset)
//------------------------------------------------------------------------------

module qeciphy_tx_boundary_gen (
    input logic clk_i,                    // Clock input
    input logic rst_n_i,                  // Active-low reset
    output logic faw_boundary_o,          // FAW boundary signal (every 64 cycles)
    output logic almost_faw_boundary_o,   // Early FAW boundary warning (1 cycle ahead)
    output logic crc_boundary_o           // CRC boundary signal (every 7 cycles, gated)
);
   
   // FAW Boundary Generation
   logic [5:0] faw_counter;            // Counter for 64 cycle FAW frame
   logic almost_faw_boundary;          // Internal almost FAW boundary signal
   logic faw_boundary;                 // Internal FAW boundary signal

   // CRC Boundary Generation  
   logic [2:0] crc_counter;            // Counter for 7 cycle CRC frame
   logic almost_crc_boundary;          // Internal almost CRC boundary signal
   logic crc_boundary;                 // Internal CRC boundary signal
   logic crc_boundary_en;              // Enable for CRC boundary output

   //--------------------------------------------------------------------------
   // Output Assignments
   //--------------------------------------------------------------------------
   assign almost_faw_boundary_o = almost_faw_boundary;
   assign faw_boundary_o        = faw_boundary;
   assign crc_boundary_o        = crc_boundary_en ? crc_boundary : 1'b0;  // Gated CRC boundary

   //--------------------------------------------------------------------------
   // FAW Counter Logic
   //--------------------------------------------------------------------------
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_counter <= '0;
      end else if (almost_faw_boundary) begin
         faw_counter <= '0;                // Reset when reaching end of frame
      end else begin
         faw_counter <= faw_counter + 6'd1;  // Increment every cycle
      end
   end

   //--------------------------------------------------------------------------
   // FAW Boundary Generation
   //--------------------------------------------------------------------------
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         almost_faw_boundary <= 1'b0;
      end else begin
         almost_faw_boundary <= (faw_counter == 6'h3E);
      end
   end

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         faw_boundary <= 1'b0;
      end else begin
         faw_boundary <= almost_faw_boundary; // Delayed by 1 cycle
      end
   end

   //--------------------------------------------------------------------------
   // CRC Boundary Enable Logic
   //--------------------------------------------------------------------------
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_boundary_en <= 1'b0;
      end else if (faw_boundary) begin
         crc_boundary_en <= 1'b1;  // Enable on first FAW boundary and stay enabled
      end
   end

   //--------------------------------------------------------------------------
   // CRC Counter Logic  
   //--------------------------------------------------------------------------
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_counter <= 3'd0;
      end else if (almost_faw_boundary || almost_crc_boundary) begin
         crc_counter <= 3'd0;  // Reset on either boundary type
      end else begin
         crc_counter <= crc_counter + 3'd1;  // Increment every cycle
      end
   end

   //--------------------------------------------------------------------------
   // CRC Boundary Generation
   //--------------------------------------------------------------------------
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         almost_crc_boundary <= 1'b0;
      end else begin
         almost_crc_boundary <= (crc_counter == 3'h5);  
      end
   end

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         crc_boundary <= 1'b0;
      end else begin
         crc_boundary <= almost_crc_boundary;  // Delayed by 1 cycle
      end
   end

endmodule
