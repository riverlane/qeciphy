// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef QECIPHY_UVMTB_SV_
`define QECIPHY_UVMTB_SV_

//------------------------------------------------------------------------------------------------------------------------------------------
// Module: qeciphy_uvmtb
//
// Abstract:
//------------------------------------------------------------------------------------------------------------------------------------------
module qeciphy_uvmtb ();

   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // Import all the UVM tests etc.
   import qeciphy_env_pkg::*;
   import qeciphy_test_pkg::*;
   import qeciphy_uvmtb_pkg::*;

   logic dut_aclk;
   logic dut_rclk;
   logic dut_fclk;
   logic dut_arst_n;

   logic [63:0] dut_tx_tdata;
   logic        dut_tx_tvalid;
   logic        dut_tx_tready;
   logic [63:0] dut_rx_tdata;
   logic        dut_rx_tvalid;
   logic        dut_rx_tready;

   logic [ 3:0] dut_status;
   logic [ 3:0] dut_ecode;

   logic tbphy_aclk;
   logic tbphy_rclk;
   logic tbphy_fclk;
   logic tbphy_arst_n;

   logic [63:0] tbphy_tx_tdata;
   logic        tbphy_tx_tvalid;
   logic        tbphy_tx_tready;
   logic [63:0] tbphy_rx_tdata;
   logic        tbphy_rx_tvalid;
   logic        tbphy_rx_tready;

   logic [ 3:0] tbphy_status;
   logic [ 3:0] tbphy_ecode;

   wire logic dut_txp;
   wire logic dut_txn;
   wire logic dut_rxp;
   wire logic dut_rxn;
   wire logic tbphy_txp;
   wire logic tbphy_txn;
   wire logic tbphy_rxp;
   wire logic tbphy_rxn;

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Instance the DUT and connect to TB signals.
   //----------------------------------------------------------------------------------------------------------------------------------------
   QECIPHY #(.GT_TYPE(`GT_TYPE)) i_dut (
      .RCLK      (dut_rclk),
      .FCLK      (dut_fclk),
      .ACLK      (dut_aclk),
      .ARSTn     (dut_arst_n),
      .TX_TDATA  (dut_tx_tdata),
      .TX_TVALID (dut_tx_tvalid),
      .TX_TREADY (dut_tx_tready),
      .RX_TDATA  (dut_rx_tdata),
      .RX_TVALID (dut_rx_tvalid),
      .RX_TREADY (dut_rx_tready),
      .STATUS    (dut_status),
      .ECODE     (dut_ecode),
      .GT_RX_P   (dut_rxp),
      .GT_RX_N   (dut_rxn),
      .GT_TX_P   (dut_txp),
      .GT_TX_N   (dut_txn)
   );
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Instance the second PHY to be used by tests to transfer data to/from DUT.
   //----------------------------------------------------------------------------------------------------------------------------------------
   QECIPHY #(.GT_TYPE(`GT_TYPE)) i_tbphy (
      .RCLK      (tbphy_rclk),
      .FCLK      (tbphy_fclk),
      .ACLK      (tbphy_aclk),
      .ARSTn     (tbphy_arst_n),
      .TX_TDATA  (tbphy_tx_tdata),
      .TX_TVALID (tbphy_tx_tvalid),
      .TX_TREADY (tbphy_tx_tready),
      .RX_TDATA  (tbphy_rx_tdata),
      .RX_TVALID (tbphy_rx_tvalid),
      .RX_TREADY (tbphy_rx_tready),
      .STATUS    (tbphy_status),
      .ECODE     (tbphy_ecode),
      .GT_RX_P   (tbphy_rxp),
      .GT_RX_N   (tbphy_rxn),
      .GT_TX_P   (tbphy_txp),
      .GT_TX_N   (tbphy_txn)
   );
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Instance wrapper connected to internal nets (can then be connected to agents, miscio_if etc. using hierarchical connects).
   //----------------------------------------------------------------------------------------------------------------------------------------
   qeciphy_uvmtb_internals i_internals();
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Instance all interfaces that connect to DUT signals.
   //----------------------------------------------------------------------------------------------------------------------------------------
   qeciphy_env_miscio_if i_miscio_if(
      .dut_aclk   (dut_aclk),   .dut_rclk   (dut_rclk),   .dut_fclk   (dut_fclk),   .dut_arst_n   (dut_arst_n),
      .tbphy_aclk (tbphy_aclk), .tbphy_rclk (tbphy_rclk), .tbphy_fclk (tbphy_fclk), .tbphy_arst_n (tbphy_arst_n)
   );
   assign i_miscio_if.dut_status   = dut_status;
   assign i_miscio_if.dut_ecode    = dut_ecode;
   assign i_miscio_if.tbphy_status = tbphy_status;
   assign i_miscio_if.tbphy_ecode  = tbphy_ecode;

   riv_clk_rst_gen_vip_if    i_dut_aclk_if( .clk_reqs('{1'b1}), .clks('{dut_aclk}), .resets('{dut_arst_n}) );
   riv_clk_rst_gen_vip_if    i_dut_rclk_if( .clk_reqs('{1'b1}), .clks('{dut_rclk}), .resets() );
   riv_clk_rst_gen_vip_if    i_dut_fclk_if( .clk_reqs('{1'b1}), .clks('{dut_fclk}), .resets() );

   riv_rdy_vld_sink_bfm#(.WIDTH(64), .VIF_NAME("dut_axis_rx_vif")) i_dut_axis_rx_bfm(
      .clk   (dut_aclk),
      .rst_n (dut_arst_n),
      .data  (dut_rx_tdata),
      .valid (dut_rx_tvalid),
      .ready (dut_rx_tready)
   );

   riv_rdy_vld_source_bfm#(.WIDTH(64), .VIF_NAME("dut_axis_tx_vif")) i_dut_axis_tx_bfm(
      .clk   (dut_aclk),
      .rst_n (dut_arst_n),
      .data  (dut_tx_tdata),
      .valid (dut_tx_tvalid),
      .ready (dut_tx_tready)
   );
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Instance all interfaces that connect to TB PHY signals.
   //----------------------------------------------------------------------------------------------------------------------------------------
   riv_clk_rst_gen_vip_if  i_tbphy_aclk_if( .clk_reqs('{1'b1}), .clks('{tbphy_aclk}), .resets('{tbphy_arst_n}) );
   riv_clk_rst_gen_vip_if  i_tbphy_rclk_if( .clk_reqs('{1'b1}), .clks('{tbphy_rclk}), .resets() );
   riv_clk_rst_gen_vip_if  i_tbphy_fclk_if( .clk_reqs('{1'b1}), .clks('{tbphy_fclk}), .resets() );

   riv_rdy_vld_sink_bfm#(.WIDTH(64), .VIF_NAME("tbphy_axis_rx_vif")) i_tbphy_axis_rx_bfm(
      .clk   (tbphy_aclk),
      .rst_n (tbphy_arst_n),
      .data  (tbphy_rx_tdata),
      .valid (tbphy_rx_tvalid),
      .ready (tbphy_rx_tready)
   );

   riv_rdy_vld_source_bfm#(.WIDTH(64), .VIF_NAME("tbphy_axis_tx_vif")) i_tbphy_axis_tx_bfm(
      .clk   (tbphy_aclk),
      .rst_n (tbphy_arst_n),
      .data  (tbphy_tx_tdata),
      .valid (tbphy_tx_tvalid),
      .ready (tbphy_tx_tready)
   );
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   //----------------------------------------------------------------------------------------------------------------------------------------
   riv_diff_pair_connector_vip_if i_dut2tbphy_conn_if( .rx_p(dut_txp),   .rx_n(dut_txn),   .tx_p(tbphy_rxp), .tx_n(tbphy_rxn) );
   riv_diff_pair_connector_vip_if i_tbphy2dut_conn_if( .rx_p(tbphy_txp), .rx_n(tbphy_txn), .tx_p(dut_rxp),   .tx_n(dut_rxn)   );
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Add all interfaces into UVM ConfigDB and then start the UVM test.
   //----------------------------------------------------------------------------------------------------------------------------------------
   initial begin
      uvm_config_db#(virtual qeciphy_env_miscio_if)::set(uvm_root::get(),          "", "miscio_vif",         i_miscio_if);
      uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::set(uvm_root::get(),         "", "dut_aclk_vif",       i_dut_aclk_if);
      uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::set(uvm_root::get(),         "", "dut_rclk_vif",       i_dut_rclk_if);
      uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::set(uvm_root::get(),         "", "dut_fclk_vif",       i_dut_fclk_if);
      uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::set(uvm_root::get(),         "", "tbphy_aclk_vif",     i_tbphy_aclk_if);
      uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::set(uvm_root::get(),         "", "tbphy_rclk_vif",     i_tbphy_rclk_if);
      uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::set(uvm_root::get(),         "", "tbphy_fclk_vif",     i_tbphy_fclk_if);
      uvm_config_db#(virtual riv_diff_pair_connector_vip_if)::set(uvm_root::get(), "", "dut2tbphy_conn_vif", i_dut2tbphy_conn_if);
      uvm_config_db#(virtual riv_diff_pair_connector_vip_if)::set(uvm_root::get(), "", "tbphy2dut_conn_vif", i_tbphy2dut_conn_if);
      run_test();
   end
   //----------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Optionally dump the sim variable for waveform display
   //---------------------------------------------------------------------------------------------------------------------------------------
   `ifdef WAVES_FSDB
   initial begin
      $fsdbDumpfile("qeciphy_uvmtb");
      $fsdbDumpvars;
   end  //  initial $wlfdumpvars();
   `endif
   //---------------------------------------------------------------------------------------------------------------------------------------

endmodule : qeciphy_uvmtb
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_UVMTB_SV_
