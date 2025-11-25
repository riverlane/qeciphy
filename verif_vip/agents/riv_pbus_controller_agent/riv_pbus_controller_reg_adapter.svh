
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_REG_ADAPTER_SVH_
`define RIV_PBUS_CONTROLLER_REG_ADAPTER_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_pbus_controller_reg_adapter
//
// An adapter is not instanced in the agent but the class is defined for use in environments using this agent.
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_pbus_controller_reg_adapter extends uvm_reg_adapter;

   `uvm_object_utils(riv_pbus_controller_reg_adapter)

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name = "");
      super.new(name);
      // HINT: Modify the following according to agent requirements.
      supports_byte_enable = 1'b0;
      provides_responses   = 1'b0;
   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: reg2bus
   //
   // Convert a uvm_reg_bus_op into a riv_pbus_controller_txn item.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
      const string msg_id = {get_type_name(), ".reg2bus"};

      riv_pbus_controller_txn  txn;

      txn = riv_pbus_controller_txn::type_id::create("txn", .contxt(get_full_name()));

      `uvm_fatal(msg_id, "This reg_adapter needs creating")

      return txn;

   endfunction : reg2bus
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: bus2reg
   //
   // Convert a riv_pbus_controller_txn item into a uvm_reg_bus_op.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
      const string msg_id = {get_type_name(), ".reg2bus"};

      riv_pbus_controller_txn  txn;

      if (! $cast(txn, bus_item)) `uvm_fatal(msg_id, "Failed to cast bus_item to riv_pbus_controller_txn class.")

      `uvm_fatal(msg_id, "This reg_adapter needs creating")

      rw.status = UVM_IS_OK;

   endfunction : bus2reg
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_pbus_controller_reg_adapter
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_REG_ADAPTER_SVH_
