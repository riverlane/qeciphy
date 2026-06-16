// SPDX-License-Identifier: BSD-2-Clause
// -----------------------------------------------------------------------------
// File        : tennm_lcell_comb.sv
// Description : Lint stub for Altera Agilex (Tennm) LUT primitive.
//               Declares the module interface for tooling convenience only.
//               No functional implementation is provided.
//
// Copyright (c) 2025 Riverlane Ltd.
// This file is not affiliated with or endorsed by Altera Corporation.
// The module names and ports are reproduced solely for build compatibility.
// -----------------------------------------------------------------------------

module tennm_lcell_comb #(
    parameter [63:0] lut_mask     = 64'h0,
    parameter        extended_lut = "off",
    parameter        shared_arith = "off"
) (
    input  logic dataa,
    input  logic datab,
    input  logic datac,
    input  logic datad,
    input  logic datae,
    input  logic dataf,
    input  logic datag,
    input  logic datah,
    input  logic cin,
    input  logic sharein,
    output logic sumout,
    output logic cout,
    output logic shareout,
    output logic combout
);

   assign combout  = '0;
   assign sumout   = '0;
   assign cout     = '0;
   assign shareout = '0;

endmodule
