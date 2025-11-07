// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// 4-bit Down Counter Primitive
//------------------------------------------------------------------------------
// This module implements a 4-bit down counter that can roll over from 0 to 0xF.
//
// Behavior:
// - Counts down: value -> value-1 -> ... -> 1 -> 0 -> 0xF -> 0xE -> ... -> 1
// - 'done' asserted when count==0
// - Loading zero keeps 'done' high (no counting needed)
//------------------------------------------------------------------------------

module riv_counter_prim (
    input  logic       clk,     // Clock
    input  logic       rst_n,   // Active-low reset
    input  logic [3:0] value,   // Initial value to load
    input  logic       load,    // Load new value
    input  logic       enable,  // Enable counting
    output logic       done     // Asserted when count reaches zero
);

   logic [3:0] count;
   logic value_is_zero;

   assign value_is_zero = ~|value;

   // Counter logic: loads value or decrements when enabled
   always_ff @(posedge clk) begin
      if (~rst_n) begin
         count <= '0;
      end else if (load) begin
         count <= value;
      end else if (enable) begin
         count <= count - 4'd1;  // Rolls over: 0x0 -> 0xF
      end
   end

   // Done signal logic:
   // - De-asserted at reset
   // - Asserted when zero value is loaded
   // - Asserted when count reaches zero
   always_ff @(posedge clk) begin
      if (~rst_n) begin
         done <= 1'b0;
      end else if (load) begin
         done <= value_is_zero;
      end else if (done && enable) begin
         done <= 1'b0;  // Clear done when rolling over
      end else if (enable) begin
         done <= ~|count[3:1] && count[0];
      end
   end

endmodule
