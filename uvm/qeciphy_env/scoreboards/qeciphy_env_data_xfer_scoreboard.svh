//------------------------------------------------------------------------------------------------------------------------------------------
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_ENV_DATA_XFER_SCOREBOARD_SVH_
`define QECIPHY_ENV_DATA_XFER_SCOREBOARD_SVH_

// Class: qeciphy_env_data_xfer_scoreboard
//
// Abstract:
// Collect data transmitted by a ready-valid source and check that it gets to the associated sink.
// Assumes that the reported transactions only contain a single data word (agent monitors do this).
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_env_data_xfer_scoreboard extends uvm_scoreboard;

   int  m_num_errors = 0;   // Number of scoreboard errors detected.
   int  m_num_source_words;
   int  m_num_sink_words;
   bit  m_enable_data_checks;

   `uvm_component_utils_begin(qeciphy_env_data_xfer_scoreboard)
      `uvm_field_int(m_num_errors,         UVM_DEFAULT | UVM_UNSIGNED)
      `uvm_field_int(m_num_source_words,   UVM_DEFAULT | UVM_UNSIGNED)
      `uvm_field_int(m_num_sink_words,     UVM_DEFAULT | UVM_UNSIGNED)
      `uvm_field_int(m_enable_data_checks, UVM_DEFAULT | UVM_BIN)
   `uvm_component_utils_end

   // Pointer to miscio interface to all scoreboard to monitor status signals.
   virtual qeciphy_env_miscio_if m_miscio_vif;

   // Analysis ports to receive transaction items (uvm_analysis_imp_* classes declared in qeciphy_env_common).
   uvm_analysis_imp_axis_sink_ap#(riv_rdy_vld_sink_txn,     qeciphy_env_data_xfer_scoreboard) axis_sink_ap_imp;
   uvm_analysis_imp_axis_source_ap#(riv_rdy_vld_source_txn, qeciphy_env_data_xfer_scoreboard) axis_source_ap_imp;

   // FIFO to buffer up transmitted data until it can be compared with received data.
   uvm_tlm_analysis_fifo #(riv_rdy_vld_source_txn) m_source_fifo;

   qeciphy_env_config  m_config;    // Config object for the agent (fetched from ConfigDB).

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function new(string name, uvm_component parent);

      super.new(name, parent);

      // Create analysis port implementations and analysis FIFO..
      axis_sink_ap_imp   = new("axis_sink_ap_imp",   this);
      axis_source_ap_imp = new("axis_source_ap_imp", this);
      m_source_fifo      = new("m_source_fifo",      this);

   endfunction : new
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_phase
   //
   // Get the config object from ConfigDB and create any other objects needed by this scoreboard.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void build_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".build_phase"};

      if (! uvm_config_db#(qeciphy_env_config)::get(this, "", "config", m_config) ) begin
         `uvm_fatal(msg_id, "Can't find field 'config' in ConfigDB")
      end

   endfunction : build_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: connect_phase
   //
   // Connect up all analysis ports, sub-sequencers etc. (all sub-components are built by now).
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void connect_phase(uvm_phase phase);
      const string msg_id = { get_type_name(), ".connect_phase" };

      m_miscio_vif = m_config.m_vifs.miscio_vif;

   endfunction : connect_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: run_phase
   //
   // Wait for new transactions (or any other events, such as signal changes on the interface) and act upon them.
   // Collection and comparison of data is done in the write_* methods.
   // The main job here is to detect and react to error conditions by flushing FIFOs and disabling data comparison until after next reset.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_phase(uvm_phase phase);
      const string        msg_id = {get_type_name(), ".run_phase"};
      qeciphy_error_enum  ecode;
      qeciphy_state_enum  state;

      m_num_source_words   = 0;
      m_num_sink_words     = 0;
      wait (m_miscio_vif.dut_arst_n === 1'b0);

      forever begin

         wait (m_miscio_vif.dut_arst_n === 1'b1);
         m_enable_data_checks = 1'b1;

         fork
            @(negedge m_miscio_vif.dut_arst_n);
            do begin
               @(posedge m_miscio_vif.dut_aclk);
               ecode = qeciphy_error_enum'(m_miscio_vif.dut_ecode);
               state = qeciphy_state_enum'(m_miscio_vif.dut_status);
            end while ((ecode === PHY_OK) && (state != PHY_FAULT_FATAL));
         join_any
         disable fork;

         if ((m_miscio_vif.dut_arst_n !== 1'b0) && m_enable_data_checks) begin
            `uvm_info(msg_id, $sformatf("Data checking stopped because ECODE=%0s, STATUS=%0s", ecode.name(), state.name()), UVM_LOW)
            m_enable_data_checks = 1'b0;
            m_source_fifo.flush();
         end
         wait (m_miscio_vif.dut_arst_n === 1'b0);

      end

   endtask : run_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: check_phase
   //
   // Check that all source data has been consumed.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void check_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".check_phase"};

      super.check_phase(phase);

      if (! m_source_fifo.is_empty()) begin
         `uvm_error(msg_id, $sformatf("Source FIFO still contains %0d words", m_source_fifo.size()))
         m_num_errors++;
      end

   endfunction : check_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: report_phase
   //
   // Report summary of data transferred.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void report_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".report_phase"};

      super.report_phase(phase);

      `uvm_info(
         msg_id,
         $sformatf(
            "Received %0d source words and %0d sink words. Number of errors = %0d",
            m_num_source_words, m_num_sink_words, m_num_errors
            ),
         UVM_LOW
      )

   endfunction : report_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Capture transmitted data from AXI-Stream source and buffer in FIFO for later comparison.
   // NOTE: Whilst the m_data fields in source txns are arrays, monitored txns only contain 1 data word per txn.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void write_axis_source_ap(riv_rdy_vld_source_txn t);
      const string msg_id = {get_type_name(), ".write_axis_source_ap"};

      // If checking is disabled, then ignore new data.
      if (! m_enable_data_checks) return;

      // Just ignore any aborted transactions (no data transferred - usually because power-down caused ready to drop without valid).
      if (t.m_data.size() == 0) begin
         `uvm_info(msg_id, $sformatf("Aborted source txn detected. Txn will be skipped."), UVM_HIGH)
         return;
      end

      // Check that txn contains only 1 data word (monitors expected to capture one word at a time).
      if (t.m_data.size() > 1) begin
         `uvm_error(msg_id, $sformatf("Source data doesn't contain single word (%0d). Txn will be skipped.", t.m_data.size()))
         m_num_errors++;
         return;
      end
      m_num_source_words++;

      m_source_fifo.write(t);
      `uvm_info(msg_id, $sformatf("Data txd = 0x%016X", t.m_data[0]), UVM_HIGH)

   endfunction : write_axis_source_ap
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Check received data from AXI-Stream sink against data transmitted from source.
   // NOTE: Whilst the m_data fields in source and sink txns are arrays, monitored txns only contain 1 data word per txn.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void write_axis_sink_ap(riv_rdy_vld_sink_txn t);
      const string            msg_id = {get_type_name(), ".write_axis_sink_ap"};
      riv_rdy_vld_source_txn  source_txn;

      // If checking is disabled, then ignore new data.
      if (! m_enable_data_checks) return;

      // Just ignore any aborted transactions (no data transferred - usually because power-down caused ready to drop without valid).
      if (t.m_data.size() == 0) begin
         `uvm_info(msg_id, $sformatf("Aborted sink txn detected. Txn will be skipped."), UVM_HIGH)
         return;
      end

      // Check that txn contains only 1 data word (monitors expected to capture one word at a time).
      if (t.m_data.size() > 1) begin
         `uvm_error(msg_id, $sformatf("Sink data doesn't contain single word (%0d). Txn will be skipped.", t.m_data.size()))
         m_num_errors++;
         return;
      end
      m_num_sink_words++;

      // Check that there is expected data to compare with and then fetch it from the buffer.
      if (! m_source_fifo.try_get(source_txn)) begin
         `uvm_error(msg_id, $sformatf("Failed to get a source txn (%0d txns in source FIFO)", m_source_fifo.size()))
         m_num_errors++;
         return;
      end

      // Check that sink data matches the next recorded source data.
      if (source_txn.m_data[0] != t.m_data[0]) begin
         `uvm_error(msg_id, $sformatf("Sink data (0x%016X) != source data (0x%016X)", t.m_data[0], source_txn.m_data[0]))
         m_num_errors++;
         return;
      end
      `uvm_info(msg_id, $sformatf("Sink data (0x%016X) matches source data", t.m_data[0]), UVM_HIGH)

   endfunction : write_axis_sink_ap
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_env_data_xfer_scoreboard
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_ENV_DATA_XFER_SCOREBOARD_SVH_
