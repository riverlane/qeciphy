// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Evan Sun
//
// GT COMMON (QPLL0) wrapper for GTY quads, instantiated once per physical GT quad so
// that multiple QECIPHY lanes in the quad can share one QPLL0. Used by QECIPHY_QUAD
// when transceiver.gt_common is "external". QPLL1 is unused and held powered down.
//
// The GTYE4_COMMON attributes come from src/qeciphy_gty_common_attrs.svh, which
// render-design extracts from the wizard's generated COMMON wrapper for this profile
// (see scripts/gen_gt_common_attrs.py). The primitive's defaults are not valid here -
// e.g. the default QPLL0CLKOUT_RATE of FULL runs the channels at twice their line rate.

`include "qeciphy_build_cfg_pkg.sv"

module qeciphy_gty_common #(
    // Simulation attributes
    parameter WRAPPER_SIM_GTRESET_SPEEDUP = "TRUE",
    parameter WRAPPER_SIM_MODE            = "FAST"
) (
    input  logic [2:0] qpll0refclksel_in,
    input  logic       gtrefclk00_in,
    input  logic       gtrefclk01_in,
    output logic       qpll0lock_out,
    input  logic       qpll0lockdetclk_in,
    output logic       qpll0outclk_out,
    output logic       qpll0outrefclk_out,
    output logic       qpll0refclklost_out,
    input  logic       qpll0reset_in
);

   GTYE4_COMMON #(
       // Simulation attributes
       .SIM_RESET_SPEEDUP(WRAPPER_SIM_GTRESET_SPEEDUP),
       .SIM_MODE(WRAPPER_SIM_MODE),
       .SIM_DEVICE("ULTRASCALE_PLUS")
`ifdef QECIPHY_GT_COMMON_EXTERNAL
`ifndef VERILATOR
       // Wizard-chosen attributes (see file header); the Verilator lint stub doesn't declare them.
       `include "qeciphy_gty_common_attrs.svh"
`endif
`endif
   ) gtye4_common_i (
       //----------- Common Block - Dynamic Reconfiguration Port (DRP) -----------
       .DRPADDR(16'h0000),
       .DRPCLK(1'b0),
       .DRPDI(16'h0000),
       .DRPDO(),
       .DRPEN(1'b0),
       .DRPRDY(),
       .DRPWE(1'b0),
       //-------------------- Common Block - Ref Clock Ports ---------------------
       .GTGREFCLK0(1'b0),
       .GTGREFCLK1(1'b0),
       .GTNORTHREFCLK00(1'b0),
       .GTNORTHREFCLK01(1'b0),
       .GTNORTHREFCLK10(1'b0),
       .GTNORTHREFCLK11(1'b0),
       .GTREFCLK00(gtrefclk00_in),
       .GTREFCLK01(gtrefclk01_in),
       .GTREFCLK10(1'b0),
       .GTREFCLK11(1'b0),
       .GTSOUTHREFCLK00(1'b0),
       .GTSOUTHREFCLK01(1'b0),
       .GTSOUTHREFCLK10(1'b0),
       .GTSOUTHREFCLK11(1'b0),
       //-------------------------- PCIe rate switch ------------------------------
       .PCIERATEQPLL0(3'b000),
       .PCIERATEQPLL1(3'b000),
       //----------------------- Common Block - QPLL0 Ports -----------------------
       .QPLL0CLKRSVD0(1'b0),
       .QPLL0CLKRSVD1(1'b0),
       .QPLL0FBDIV(8'h00),
       .QPLL0OUTCLK(qpll0outclk_out),
       .QPLL0OUTREFCLK(qpll0outrefclk_out),
       .QPLL0LOCK(qpll0lock_out),
       .QPLL0LOCKDETCLK(qpll0lockdetclk_in),
       .QPLL0LOCKEN(1'b1),
       .QPLL0PD(1'b0),
       .QPLL0REFCLKLOST(qpll0refclklost_out),
       .QPLL0REFCLKSEL(qpll0refclksel_in),
       .QPLL0RESET(qpll0reset_in),
       .QPLL0FBCLKLOST(),
       //----------------------- Common Block - QPLL1 Ports -----------------------
       // QPLL1 unused by QECIPHY - power it down and hold it in reset.
       .QPLL1CLKRSVD0(1'b0),
       .QPLL1CLKRSVD1(1'b0),
       .QPLL1FBDIV(8'h00),
       .QPLL1OUTCLK(),
       .QPLL1OUTREFCLK(),
       .QPLL1LOCK(),
       .QPLL1LOCKDETCLK(1'b0),
       .QPLL1LOCKEN(1'b0),
       .QPLL1PD(1'b1),
       .QPLL1REFCLKLOST(),
       .QPLL1REFCLKSEL(3'b001),
       .QPLL1RESET(1'b1),
       .QPLL1FBCLKLOST(),
       //------------------------------- QPLL Ports -------------------------------
       .QPLLRSVD1(8'h00),
       .QPLLRSVD2(5'b00000),
       .QPLLRSVD3(5'b00000),
       .QPLLRSVD4(8'h00),
       .QPLLDMONITOR0(),
       .QPLLDMONITOR1(),
       .REFCLKOUTMONITOR0(),
       .REFCLKOUTMONITOR1(),
       //-------------------- Fractional-N synthesizer (SDM) ---------------------
       // Unused by QECIPHY - fractional-N feedback divider left disabled.
       .SDM0DATA(25'h0000000),
       .SDM0RESET(1'b0),
       .SDM0TOGGLE(1'b0),
       .SDM0WIDTH(2'b00),
       .SDM0FINALOUT(),
       .SDM0TESTDATA(),
       .SDM1DATA(25'h0000000),
       .SDM1RESET(1'b0),
       .SDM1TOGGLE(1'b0),
       .SDM1WIDTH(2'b00),
       .SDM1FINALOUT(),
       .SDM1TESTDATA(),
       //---------------- User Bitstream (internal debug hub) --------------------
       // Unused by QECIPHY - disable the internal calibration/debug microcontroller interface.
       .UBCFGSTREAMEN(1'b0),
       .UBENABLE(1'b0),
       .UBDO(16'h0000),
       .UBDRDY(1'b0),
       .UBGPI(2'b00),
       .UBINTR(2'b00),
       .UBIOLMBRST(1'b0),
       .UBMBRST(1'b0),
       .UBMDMCAPTURE(1'b0),
       .UBMDMDBGRST(1'b0),
       .UBMDMDBGUPDATE(1'b0),
       .UBMDMREGEN(4'b0000),
       .UBMDMSHIFT(1'b0),
       .UBMDMSYSRST(1'b0),
       .UBMDMTCK(1'b0),
       .UBMDMTDI(1'b0),
       .UBDADDR(),
       .UBDEN(),
       .UBDI(),
       .UBDWE(),
       .UBMDMTDO(),
       .UBRSVDOUT(),
       .UBTXUART(),
       //------------------------------- Bias/RCAL ---------------------------------
       .BGBYPASSB(1'b1),
       .BGMONITORENB(1'b1),
       .BGPDB(1'b1),
       .BGRCALOVRD(5'b10000),
       .BGRCALOVRDENB(1'b1),
       .PMARSVD0(8'h00),
       .PMARSVD1(8'h00),
       .PMARSVDOUT0(),
       .PMARSVDOUT1(),
       .RCALENB(1'b1),
       .RXRECCLK0SEL(),
       .RXRECCLK1SEL()
   );
endmodule  // qeciphy_gty_common
