// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef _QECIPHY_UVMTB_INTERNALS_SV_
`define _QECIPHY_UVMTB_INTERNALS_SV_

`ifndef STRINGIFY
`define STRINGIFY(x) `"x`"
`endif

`ifndef QECIPHY_ARCH
`define QECIPHY_ARCH RTL
`endif

//------------------------------------------------------------------------------------------------------------------------------------------
// Module: qeciphy_uvmtb_internals
//
// Abstract:
// Make connections from internal signals to pins which can then be connected to agents in top-level TB.
// Uses verilog hierarchical access rules to reach the internal nets, and usually only used to monitor these nets.
// Using QECIPHY_ARCH macro (defaults to RTL), different connections can be made depending on netlist type (e.g. RTL, gates, etc.).
//------------------------------------------------------------------------------------------------------------------------------------------
module qeciphy_uvmtb_internals (
   // HINT: output logic [1:0] my_port            // Description of my_port
);

   if (`STRINGIFY(`QECIPHY_ARCH) == "RTL") begin: rtl_connections
      // HINT: assign my_port = I_dut.block1.net1;
   end

   if (`STRINGIFY(`QECIPHY_ARCH) == "GATES") begin: gate_level_connections
      // HINT: assign my_port = I_dut.synth_block1.synth_net1;
   end

endmodule : qeciphy_uvmtb_internals
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // _QECIPHY_UVMTB_INTERNALS_SV_
