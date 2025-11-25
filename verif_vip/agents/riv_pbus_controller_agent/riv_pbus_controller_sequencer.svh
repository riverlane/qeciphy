
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_SEQUENCER_SVH_
`define RIV_PBUS_CONTROLLER_SEQUENCER_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_pbus_controller_sequencer
//
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_pbus_controller_sequencer extends uvm_sequencer#(.REQ(riv_pbus_controller_txn), .RSP(riv_pbus_controller_txn));

   riv_pbus_controller_config  m_config;   // Config object for the agent (fetched from ConfigDB) for sequence access via p_sequencer.

   `uvm_component_utils_begin(riv_pbus_controller_sequencer)
   `uvm_component_utils_end


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_phase
   //
   // Get the config object from ConfigDB and create any other objects needed.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void build_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".build_phase"};

      if (! uvm_config_db#(riv_pbus_controller_config)::get(this, "", "config", m_config) ) begin
         `uvm_fatal(msg_id, "Can't find field 'config' in ConfigDB")
      end

   endfunction : build_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_pbus_controller_sequencer
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_SEQUENCER_SVH_
