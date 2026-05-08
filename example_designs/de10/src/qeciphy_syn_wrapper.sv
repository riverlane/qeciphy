// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Aniket Datta, Gargi Sunil

module qeciphy_syn_wrapper (
    input logic gt_refclk_in_p,
    input logic clk_100_p,

    input  logic GT_RXP,
    input  logic GT_RXN,
    output logic GT_TXP,
    output logic GT_TXN,
    //    output logic qsfpdd0_modsel_L,
    //    output logic qsfpdd0_Initmode,
    //    input  logic qsfpdd0_modprs_L,
    //    input  logic qsfpdd0_int_L,

    // Additional signals from QSF pin assignments
    inout logic i2c_qsfpdd0_scl,
    inout logic i2c_qsfpdd0_sda,

    output logic [3:0] fpga_led


);

   logic        int_clk_250mhz;
   logic        int_clk_125mhz;
   logic        sys_clk_100;
   logic        sys_clk_200;
   logic        init_done_n;
   logic        out_systempll_synthlock_0;
   logic        out_systempll_clk_0;
   // Signal declarations
   logic        RCLK;
   logic        FCLK;
   logic        ACLK;
   logic        ARSTn;
   logic [63:0] TX_TDATA;
   logic [63:0] TX_TDATA_nxt;
   logic        TX_TVALID;
   logic        TX_TREADY;
   logic [63:0] RX_TDATA;
   logic        RX_TVALID;
   logic        RX_TREADY;
   logic        LINK_READY;
   logic        FAULT_FATAL;
   logic [ 3:0] STATUS;
   logic [ 3:0] ECODE;
   logic [ 4:0] rst_counter;
   logic [ 4:0] rst_counter_nxt;
   logic        rst_n_async;
   logic        rst_n;
   logic        clk_freerun;
   logic [ 3:0] sfp_enable;
   logic [63:0] RX_TDATA_ref;
   logic [63:0] RX_TDATA_ref_nxt;
   logic        RXDATA_error;
   logic        RXDATA_error_nxt;


   //Temporary logic
   logic [ 2:0] led;
   logic [26:0] blinky_counter;
   logic        blinky_led;

   // Debug signals for ILA and VIO
   logic [ 6:0] vio_source;


   assign rst_n = !init_done_n;
   reset_release reset_release_inst (.ninit_done(init_done_n));

   assign ACLK = sys_clk_200;
   assign FCLK = sys_clk_200;
   sys_clk_100 clk100_inst (
       .inclk (clk_100_p),   //   input,  width = 1,  inclk.clk
       .outclk(sys_clk_100)  //  output,  width = 1, outclk.clk
   );

   sys_clk_200_pll clk200_inst (
       .refclk  (sys_clk_100),  //   input,  width = 1,  refclk.clk
       .locked  (),             //  output,  width = 1,  locked.export
       .rst     (1'b0),         //   input,  width = 1,   reset.reset
       .axis_clk(sys_clk_200)   //  output,  width = 1, outclk0.clk
   );


   //This is an internal 250 MHz system clock 
   clock_configuration clock_configuration_inst (.clkout(int_clk_250mhz));
   clock_divider sys_clock_divider_inst (
       .inclk(int_clk_250mhz),
       .clock_div1x(  /* open or unconnected */),
       .clock_div2x(int_clk_125mhz)
   );

   // Connect VIO source to individual signals
   assign rst_n_async = vio_source[0];
   assign sfp_enable  = vio_source[6:3];  // Other bits of sfp_enable

   qeciphy_vio i_vio (
       .source    (vio_source),  //  output,  width = 7,    sources.source
       .source_clk(ACLK)         //   input,  width = 1, source_clk.clk
   );

   // Generate 16 cycle reset that de-asserts synchronously
   assign ARSTn           = rst_counter[4];
   assign rst_counter_nxt = ARSTn ? rst_counter : rst_counter + 5'h1;

   always_ff @(posedge ACLK or negedge rst_n) begin
      if (!rst_n) rst_counter <= 5'h0;
      else rst_counter <= rst_counter_nxt;
   end


   assign fpga_led = {blinky_led, led};  // Connect debug LEDs with extra bit
   // For debugging
   assign led[0]   = (STATUS == 4'b0100) ? 1'b1 : 1'b0;
   assign led[1]   = (ECODE == 4'b0000) ? 1'b1 : 1'b0;
   assign led[2]   = ~RXDATA_error;

   // 1-second blinky on fpga_led[3] (ACLK = 100 MHz)
   always_ff @(posedge ACLK or negedge rst_n) begin
      if (!rst_n) begin
         blinky_counter <= '0;
         blinky_led     <= 1'b0;
      end else begin
         if (blinky_counter == 27'd99_999_999) begin
            blinky_counter <= '0;
            blinky_led     <= ~blinky_led;
         end else begin
            blinky_counter <= blinky_counter + 1'b1;
         end
      end
   end


   // By the spec
   assign RX_TREADY = 1'b1;
   // Drive the transmitter QECI-PHY TX data pins
   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) TX_TVALID <= 1'b0;
      else TX_TVALID <= 1'b1;
   end

   assign TX_TDATA_nxt = TX_TREADY ? TX_TDATA + 64'h1 : TX_TDATA;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) TX_TDATA <= 'h0;
      else TX_TDATA <= TX_TDATA_nxt;
   end

   // Verify receiver data  
   assign RX_TDATA_ref_nxt = RX_TVALID ? RX_TDATA_ref + 64'h1 : RX_TDATA_ref;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) RX_TDATA_ref <= 'h0;
      else RX_TDATA_ref <= RX_TDATA_ref_nxt;
   end

   assign RXDATA_error_nxt = RX_TVALID ? (RX_TDATA_ref != RX_TDATA) : RXDATA_error;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) RXDATA_error <= 'h0;
      else RXDATA_error <= RXDATA_error_nxt;
   end


   assign RCLK = gt_refclk_in_p;
   QECIPHY i_QECIPHY (
       .RCLK       (RCLK),
       .FCLK       (FCLK),
       .ACLK       (ACLK),
       .ARSTn      (ARSTn),
       .TX_TDATA   (TX_TDATA),
       .TX_TVALID  (TX_TVALID),
       .TX_TREADY  (TX_TREADY),
       .RX_TDATA   (RX_TDATA),
       .RX_TVALID  (RX_TVALID),
       .RX_TREADY  (RX_TREADY),
       .STATUS     (STATUS),
       .ECODE      (ECODE),
       .LINK_READY (LINK_READY),
       .FAULT_FATAL(FAULT_FATAL),
       .GT_RX_P    (GT_RXP),
       .GT_RX_N    (GT_RXN),
       .GT_TX_P    (GT_TXP),
       .GT_TX_N    (GT_TXN)
   );

   // CURRENTLY UNUSED SIGNAL ASSIGNMENTS
   // I2C data lines default to High-Z (tri-state) for proper I2C operation
   assign i2c_qsfpdd0_sda = 1'bz;
   assign i2c_qsfpdd0_scl = 1'bz;



endmodule
