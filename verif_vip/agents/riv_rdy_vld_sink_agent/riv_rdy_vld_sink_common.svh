
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SINK_COMMON_SVH_
`define RIV_RDY_VLD_SINK_COMMON_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Typedefs, constants, functions and tasks for use within the riv_rdy_vld_sink_agent_pkg package.
//------------------------------------------------------------------------------------------------------------------------------------------

// Declare implementation class for monitor's analysis port.
`uvm_analysis_imp_decl(_riv_rdy_vld_sink_mon_ap)

localparam int MAX_WIDTH = `RIV_RDY_VLD_SINK_AGENT_MAX_WIDTH;

typedef logic [MAX_WIDTH - 1 : 0] rdy_vld_sink_data_t;

`endif  // RIV_RDY_VLD_SINK_COMMON_SVH_
