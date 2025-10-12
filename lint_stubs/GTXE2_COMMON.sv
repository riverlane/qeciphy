// SPDX-License-Identifier: None
// -----------------------------------------------------------------------------
// File        : GTXE2_COMMON.sv
// Description : Lint stub for Xilinx GTXE2_COMMON module.
//               Declares the module interface for tooling convenience only.
//               No functional implementation is provided.
// 
// Copyright (c) 2025 Riverlane Ltd.
// This file is not affiliated with or endorsed by Xilinx Inc. or AMD.
// The module names and ports are reproduced solely for build compatibility.
// -----------------------------------------------------------------------------

module GTXE2_COMMON #(
    parameter SIM_RESET_SPEEDUP        = "TRUE",
    parameter SIM_QPLLREFCLK_SEL       = 3'b001,
    parameter SIM_VERSION              = "4.0",
    parameter BIAS_CFG                 = 64'h0000040000001000,
    parameter COMMON_CFG               = 32'h00000000,
    parameter QPLL_CFG                 = 27'h0680181,
    parameter QPLL_CLKOUT_CFG          = 4'b0000,
    parameter QPLL_COARSE_FREQ_OVRD    = 6'b010000,
    parameter QPLL_COARSE_FREQ_OVRD_EN = 1'b0,
    parameter QPLL_CP                  = 10'b0000011111,
    parameter QPLL_CP_MONITOR_EN       = 1'b0,
    parameter QPLL_DMONITOR_SEL        = 1'b0,
    parameter QPLL_FBDIV               = 10'b0101110000,
    parameter QPLL_FBDIV_MONITOR_EN    = 1'b0,
    parameter QPLL_FBDIV_RATIO         = 1'b1,
    parameter QPLL_INIT_CFG            = 24'h000006,
    parameter QPLL_LOCK_CFG            = 16'h21E8,
    parameter QPLL_LPF                 = 4'b1111,
    parameter QPLL_REFCLK_DIV          = 1
) (
    input  logic [ 7:0] DRPADDR,
    input  logic        DRPCLK,
    input  logic [15:0] DRPDI,
    output logic        DRPDO,
    input  logic        DRPEN,
    output logic        DRPRDY,
    input  logic        DRPWE,
    input  logic        GTGREFCLK,
    input  logic        GTNORTHREFCLK0,
    input  logic        GTNORTHREFCLK1,
    input  logic        GTREFCLK0,
    input  logic        GTREFCLK1,
    input  logic        GTSOUTHREFCLK0,
    input  logic        GTSOUTHREFCLK1,
    output logic        QPLLDMONITOR,
    output logic        QPLLOUTCLK,
    output logic        QPLLOUTREFCLK,
    output logic        REFCLKOUTMONITOR,
    output logic        QPLLFBCLKLOST,
    output logic        QPLLLOCK,
    input  logic        QPLLLOCKDETCLK,
    input  logic        QPLLLOCKEN,
    input  logic        QPLLOUTRESET,
    input  logic        QPLLPD,
    output logic        QPLLREFCLKLOST,
    input  logic [ 2:0] QPLLREFCLKSEL,
    input  logic        QPLLRESET,
    input  logic [15:0] QPLLRSVD1,
    input  logic [ 4:0] QPLLRSVD2,
    input  logic        BGBYPASSB,
    input  logic        BGMONITORENB,
    input  logic        BGPDB,
    input  logic [ 4:0] BGRCALOVRD,
    input  logic [ 7:0] PMARSVD,
    input  logic        RCALENB
);

endmodule
