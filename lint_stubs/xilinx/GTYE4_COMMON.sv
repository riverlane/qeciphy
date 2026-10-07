// SPDX-License-Identifier: BSD-2-Clause
// -----------------------------------------------------------------------------
// File        : GTYE4_COMMON.sv
// Description : Lint stub for Xilinx GTYE4_COMMON module.
//               Declares the module interface for tooling convenience only.
//               No functional implementation is provided. Port list verified
//               against $XILINX_VIVADO/data/verilog/src/unisims/GTYE4_COMMON.v
//               (Vivado 2024.1) - see src/qeciphy_gty_common.sv for the ports
//               this repo actually drives.
//
// Copyright (c) 2026 Riverlane Ltd.
// This file is not affiliated with or endorsed by Xilinx Inc. or AMD.
// The module names and ports are reproduced solely for build compatibility.
// -----------------------------------------------------------------------------

module GTYE4_COMMON #(
    parameter SIM_RESET_SPEEDUP = "TRUE",
    parameter SIM_MODE          = "FAST",
    parameter SIM_DEVICE        = "ULTRASCALE_PLUS"
) (
    output logic [15:0] DRPDO,
    output logic        DRPRDY,
    output logic [ 7:0] PMARSVDOUT0,
    output logic [ 7:0] PMARSVDOUT1,
    output logic        QPLL0FBCLKLOST,
    output logic        QPLL0LOCK,
    output logic        QPLL0OUTCLK,
    output logic        QPLL0OUTREFCLK,
    output logic        QPLL0REFCLKLOST,
    output logic        QPLL1FBCLKLOST,
    output logic        QPLL1LOCK,
    output logic        QPLL1OUTCLK,
    output logic        QPLL1OUTREFCLK,
    output logic        QPLL1REFCLKLOST,
    output logic [ 7:0] QPLLDMONITOR0,
    output logic [ 7:0] QPLLDMONITOR1,
    output logic        REFCLKOUTMONITOR0,
    output logic        REFCLKOUTMONITOR1,
    output logic [ 1:0] RXRECCLK0SEL,
    output logic [ 1:0] RXRECCLK1SEL,
    output logic [ 3:0] SDM0FINALOUT,
    output logic [14:0] SDM0TESTDATA,
    output logic [ 3:0] SDM1FINALOUT,
    output logic [14:0] SDM1TESTDATA,
    output logic [15:0] UBDADDR,
    output logic        UBDEN,
    output logic [15:0] UBDI,
    output logic        UBDWE,
    output logic        UBMDMTDO,
    output logic        UBRSVDOUT,
    output logic        UBTXUART,

    input logic        BGBYPASSB,
    input logic        BGMONITORENB,
    input logic        BGPDB,
    input logic [ 4:0] BGRCALOVRD,
    input logic        BGRCALOVRDENB,
    input logic [15:0] DRPADDR,
    input logic        DRPCLK,
    input logic [15:0] DRPDI,
    input logic        DRPEN,
    input logic        DRPWE,
    input logic        GTGREFCLK0,
    input logic        GTGREFCLK1,
    input logic        GTNORTHREFCLK00,
    input logic        GTNORTHREFCLK01,
    input logic        GTNORTHREFCLK10,
    input logic        GTNORTHREFCLK11,
    input logic        GTREFCLK00,
    input logic        GTREFCLK01,
    input logic        GTREFCLK10,
    input logic        GTREFCLK11,
    input logic        GTSOUTHREFCLK00,
    input logic        GTSOUTHREFCLK01,
    input logic        GTSOUTHREFCLK10,
    input logic        GTSOUTHREFCLK11,
    input logic [ 2:0] PCIERATEQPLL0,
    input logic [ 2:0] PCIERATEQPLL1,
    input logic [ 7:0] PMARSVD0,
    input logic [ 7:0] PMARSVD1,
    input logic        QPLL0CLKRSVD0,
    input logic        QPLL0CLKRSVD1,
    input logic [ 7:0] QPLL0FBDIV,
    input logic        QPLL0LOCKDETCLK,
    input logic        QPLL0LOCKEN,
    input logic        QPLL0PD,
    input logic [ 2:0] QPLL0REFCLKSEL,
    input logic        QPLL0RESET,
    input logic        QPLL1CLKRSVD0,
    input logic        QPLL1CLKRSVD1,
    input logic [ 7:0] QPLL1FBDIV,
    input logic        QPLL1LOCKDETCLK,
    input logic        QPLL1LOCKEN,
    input logic        QPLL1PD,
    input logic [ 2:0] QPLL1REFCLKSEL,
    input logic        QPLL1RESET,
    input logic [ 7:0] QPLLRSVD1,
    input logic [ 4:0] QPLLRSVD2,
    input logic [ 4:0] QPLLRSVD3,
    input logic [ 7:0] QPLLRSVD4,
    input logic        RCALENB,
    input logic [24:0] SDM0DATA,
    input logic        SDM0RESET,
    input logic        SDM0TOGGLE,
    input logic [ 1:0] SDM0WIDTH,
    input logic [24:0] SDM1DATA,
    input logic        SDM1RESET,
    input logic        SDM1TOGGLE,
    input logic [ 1:0] SDM1WIDTH,
    input logic        UBCFGSTREAMEN,
    input logic [15:0] UBDO,
    input logic        UBDRDY,
    input logic        UBENABLE,
    input logic [ 1:0] UBGPI,
    input logic [ 1:0] UBINTR,
    input logic        UBIOLMBRST,
    input logic        UBMBRST,
    input logic        UBMDMCAPTURE,
    input logic        UBMDMDBGRST,
    input logic        UBMDMDBGUPDATE,
    input logic [ 3:0] UBMDMREGEN,
    input logic        UBMDMSHIFT,
    input logic        UBMDMSYSRST,
    input logic        UBMDMTCK,
    input logic        UBMDMTDI
);

   assign DRPDO = '0;
   assign DRPRDY = '0;
   assign PMARSVDOUT0 = '0;
   assign PMARSVDOUT1 = '0;
   assign QPLL0FBCLKLOST = '0;
   assign QPLL0LOCK = '0;
   assign QPLL0OUTCLK = '0;
   assign QPLL0OUTREFCLK = '0;
   assign QPLL0REFCLKLOST = '0;
   assign QPLL1FBCLKLOST = '0;
   assign QPLL1LOCK = '0;
   assign QPLL1OUTCLK = '0;
   assign QPLL1OUTREFCLK = '0;
   assign QPLL1REFCLKLOST = '0;
   assign QPLLDMONITOR0 = '0;
   assign QPLLDMONITOR1 = '0;
   assign REFCLKOUTMONITOR0 = '0;
   assign REFCLKOUTMONITOR1 = '0;
   assign RXRECCLK0SEL = '0;
   assign RXRECCLK1SEL = '0;
   assign SDM0FINALOUT = '0;
   assign SDM0TESTDATA = '0;
   assign SDM1FINALOUT = '0;
   assign SDM1TESTDATA = '0;
   assign UBDADDR = '0;
   assign UBDEN = '0;
   assign UBDI = '0;
   assign UBDWE = '0;
   assign UBMDMTDO = '0;
   assign UBRSVDOUT = '0;
   assign UBTXUART = '0;

endmodule
