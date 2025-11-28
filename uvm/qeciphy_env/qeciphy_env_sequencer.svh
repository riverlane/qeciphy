
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_ENV_SEQUENCER_SVH_
`define QECIPHY_ENV_SEQUENCER_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_env_sequencer
//
// Abstract:
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_env_sequencer extends uvm_sequencer;

   `uvm_component_utils_begin(qeciphy_env_sequencer)
   `uvm_component_utils_end

   qeciphy_env_config  m_config;   // Config object for the environment (fetched from ConfigDB) for sequence access via p_sequencer.

   // HINT: Declare handles to sub-sequencers here. Connect them in connect phase of environment. For example:
   //       subseqr_type m_subseqr;
   riv_pbus_controller_sequencer  m_dut_pbus_seqr;
   riv_rdy_vld_sink_sequencer     m_dut_axis_rx_seqr;
   riv_rdy_vld_source_sequencer   m_dut_axis_tx_seqr;
   riv_pbus_controller_sequencer  m_tbphy_pbus_seqr;
   riv_rdy_vld_sink_sequencer     m_tbphy_axis_rx_seqr;
   riv_rdy_vld_source_sequencer   m_tbphy_axis_tx_seqr;

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction : new
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_phase
   //
   // Get the config object from ConfigDB and create any other objects needed by this sequencer.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void build_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".build_phase"};

      if (! uvm_config_db#(qeciphy_env_config)::get(this, "", "config", m_config) ) begin
         `uvm_fatal(msg_id, "Can't find field 'config' in ConfigDB")
      end

   endfunction : build_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_env_sequencer
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_ENV_SEQUENCER_SVH_
