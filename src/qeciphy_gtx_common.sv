// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Dogancan Davutoglu

module qeciphy_gtx_common #(
    // Simulation attributes
    parameter WRAPPER_SIM_GTRESET_SPEEDUP = "TRUE",
    parameter SIM_QPLLREFCLK_SEL          = 3'b001
) (
    input  logic [2:0] qpllrefclksel_in,
    input  logic       gtrefclk0_in,
    input  logic       gtrefclk1_in,
    output logic       qplllock_out,
    input  logic       qplllockdetclk_in,
    output logic       qplloutclk_out,
    output logic       qplloutrefclk_out,
    output logic       qpllrefclklost_out,
    input  logic       qpllreset_in
);

   localparam QPLL_FBDIV_IN = 10'b0101110000;
   localparam QPLL_FBDIV_RATIO = 1'b1;

   GTXE2_COMMON #(
       // Simulation attributes
       .SIM_RESET_SPEEDUP (WRAPPER_SIM_GTRESET_SPEEDUP),
       .SIM_QPLLREFCLK_SEL(SIM_QPLLREFCLK_SEL),
       .SIM_VERSION       ("4.0"),

       //----------------COMMON BLOCK Attributes---------------
       .BIAS_CFG                (64'h0000040000001000),
       .COMMON_CFG              (32'h00000000),
       .QPLL_CFG                (27'h0680181),
       .QPLL_CLKOUT_CFG         (4'b0000),
       .QPLL_COARSE_FREQ_OVRD   (6'b010000),
       .QPLL_COARSE_FREQ_OVRD_EN(1'b0),
       .QPLL_CP                 (10'b0000011111),
       .QPLL_CP_MONITOR_EN      (1'b0),
       .QPLL_DMONITOR_SEL       (1'b0),
       .QPLL_FBDIV              (QPLL_FBDIV_IN),
       .QPLL_FBDIV_MONITOR_EN   (1'b0),
       .QPLL_FBDIV_RATIO        (QPLL_FBDIV_RATIO),
       .QPLL_INIT_CFG           (24'h000006),
       .QPLL_LOCK_CFG           (16'h21E8),
       .QPLL_LPF                (4'b1111),
       .QPLL_REFCLK_DIV         (1)
   ) gtxe2_common_i (
       //----------- Common Block  - Dynamic Reconfiguration Port (DRP) -----------
       .DRPADDR         (8'h00),
       .DRPCLK          (1'b0),
       .DRPDI           (16'h0000),
       .DRPDO           (),
       .DRPEN           (1'b0),
       .DRPRDY          (),
       .DRPWE           (1'b0),
       //-------------------- Common Block  - Ref Clock Ports ---------------------
       .GTGREFCLK       (1'b0),
       .GTNORTHREFCLK0  (1'b0),
       .GTNORTHREFCLK1  (1'b0),
       .GTREFCLK0       (gtrefclk0_in),
       .GTREFCLK1       (gtrefclk1_in),
       .GTSOUTHREFCLK0  (1'b0),
       .GTSOUTHREFCLK1  (1'b0),
       //----------------------- Common Block -  QPLL Ports -----------------------
       .QPLLDMONITOR    (),
       //--------------------- Common Block - Clocking Ports ----------------------
       .QPLLOUTCLK      (qplloutclk_out),
       .QPLLOUTREFCLK   (qplloutrefclk_out),
       .REFCLKOUTMONITOR(),
       //----------------------- Common Block - QPLL Ports ------------------------
       .QPLLFBCLKLOST   (),
       .QPLLLOCK        (qplllock_out),
       .QPLLLOCKDETCLK  (qplllockdetclk_in),
       .QPLLLOCKEN      (1'b1),
       .QPLLOUTRESET    (1'b0),
       .QPLLPD          (1'b0),
       .QPLLREFCLKLOST  (qpllrefclklost_out),
       .QPLLREFCLKSEL   (qpllrefclksel_in),
       .QPLLRESET       (qpllreset_in),
       .QPLLRSVD1       (16'b0000000000000000),
       .QPLLRSVD2       (5'b11111),
       //------------------------------- QPLL Ports -------------------------------
       .BGBYPASSB       (1'b1),
       .BGMONITORENB    (1'b1),
       .BGPDB           (1'b1),
       .BGRCALOVRD      (5'b11111),
       .PMARSVD         (8'b00000000),
       .RCALENB         (1'b1)
   );
endmodule  // qeciphy_gtx_common
