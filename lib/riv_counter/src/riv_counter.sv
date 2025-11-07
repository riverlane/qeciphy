// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// Ripple Down Counter
//------------------------------------------------------------------------------
// This module implements a configurable-width down counter using multiple
// 4-bit primitives arranged in a ripple configuration.
//
// Parameters:
// - WIDTH: Total counter width in bits (automatically padded to 4-bit boundary)
//
// Example operation for 8-bit counter (value=0x12):
//   Load:    prim[1]=0x1, prim[0]=0x2
//   Step 1:  prim[1]=0x1, prim[0]=0x1  (prim[0] counts)
//   Step 2:  prim[1]=0x1, prim[0]=0x0  (prim[0] counts)
//   Step 3:  prim[1]=0x0, prim[0]=0xF  (prim[0] done, prim[1] decrements)
//   ...continues until both primitives reach done state
//
// The overall 'done' signal is asserted when ALL primitives are done,
// indicating the entire counter has reached zero.
//------------------------------------------------------------------------------

module riv_counter #(
    parameter WIDTH = 16,
    localparam N_PRIM = (WIDTH + 3) / 4,    // Number of 4-bit primitives needed
    localparam PADDED_WIDTH = N_PRIM * 4     // Actual width used internally
) (
    input  logic             clk,     // Clock
    input  logic             rst_n,   // Active-low reset  
    input  logic [WIDTH-1:0] value,   // Initial value to load
    input  logic             load,    // Load new value
    input  logic             enable,  // Enable counting
    output logic             done     // Asserted when counter reaches zero
);

   logic [      N_PRIM-1:0] prim_done;  // Done signals from each primitive
   logic [      N_PRIM-1:0] prim_enable;  // Enable signals to each primitive  
   logic [PADDED_WIDTH-1:0] padded_value;  // Input value padded to 4-bit boundary
   logic                    upper_bits_done;  // Registered AND of upper primitive done signals

   // Pad the input value with zeros in the upper bits to fit 4-bit boundaries
   assign padded_value   = {{(PADDED_WIDTH - WIDTH) {1'b0}}, value};

   // Ripple enable logic: 
   // - Primitive 0 (LSBs) is enabled whenever the main enable is asserted
   // - Higher primitives are enabled only when ALL lower primitives are done
   // This creates the ripple effect where higher-order bits only change
   // when lower-order bits have completed their count cycles
   assign prim_enable[0] = enable;
   generate
      for (genvar i = 1; i < N_PRIM; i++) begin : gen_enable_cascade
         assign prim_enable[i] = &prim_done[i-1:0] & enable;
      end
   endgenerate

   // Register the upper bits done signal to reduce fan-in on the final output
   // This improves timing by breaking up large AND operations across clock cycles
   always_ff @(posedge clk) begin
      if (~rst_n) begin
         upper_bits_done <= 1'b0;
      end else begin
         if (N_PRIM == 1) begin
            upper_bits_done <= 1'b1;  // Always true for single primitive
         end else begin
            upper_bits_done <= &prim_done[N_PRIM-1:1];  // AND of all upper primitive done signals
         end
      end
   end

   // Overall done signal: asserted when ALL primitives are done
   // This indicates the entire multi-precision counter has reached zero
   assign done = prim_done[0] && upper_bits_done;

   // Instantiate the 4-bit counter primitives
   generate
      for (genvar i = 0; i < N_PRIM; i++) begin : gen_counter_prim
         riv_counter_prim i_riv_counter_prim (
             .clk   (clk),
             .rst_n (rst_n),
             .value (padded_value[i*4+3:i*4+0]),  // 4-bit slice of padded input
             .load  (load),
             .enable(prim_enable[i]),             // Ripple-enabled
             .done  (prim_done[i])
         );
      end
   endgenerate

endmodule
