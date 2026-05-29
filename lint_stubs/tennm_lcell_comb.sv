// SPDX-License-Identifier: BSD-2-Clause
// -----------------------------------------------------------------------------
// File        : tennm_lcell_comb.sv
// Description : Lint stub for Intel Agilex (Tennm) LUT primitive.
//               Declares the module interface for tooling convenience only.
//               No functional implementation is provided.
//
// Copyright (c) 2025 Riverlane Ltd.
// This file is not affiliated with or endorsed by Intel Corporation.
// The module names and ports are reproduced solely for build compatibility.
// -----------------------------------------------------------------------------

module tennm_lcell_comb #(
    parameter [63:0] lut_mask    = 64'h0,
    parameter        extended_lut = "off",
    parameter        shared_arith = "off"
) (
    input  dataa,
    input  datab,
    input  datac,
    input  datad,
    input  datae,
    input  dataf,
    input  datag,
    input  datah,
    input  cin,
    input  sharein,
    output sumout,
    output cout,
    output shareout,
    output combout
);

   assign combout  = '0;
   assign sumout   = '0;
   assign cout     = '0;
   assign shareout = '0;

endmodule
