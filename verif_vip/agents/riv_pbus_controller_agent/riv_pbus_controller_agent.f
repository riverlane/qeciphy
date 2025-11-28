
# SPDX-License-Identifier: None
# Copyright (c) 2024-2025 Riverlane Ltd.
# Original authors: jamesf-rlane, ONDWARAKA


# Search path for included files (may need changing for different simulators)
+incdir+./verif_vip/agents/riv_pbus_controller_agent
+incdir+./verif_vip/agents/riv_pbus_controller_agent/sequences

// All files to be compiled, in the correct order (bottom-up).
verif_vip/agents/riv_pbus_controller_agent/riv_pbus_controller_agent_pkg.sv
verif_vip/agents/riv_pbus_controller_agent/riv_pbus_controller_agent_if.sv
verif_vip/agents/riv_pbus_controller_agent/bfms/riv_pbus_controller_bfm.sv
verif_vip/agents/riv_pbus_controller_agent/bfms/riv_pbus_controller_monitor_bfm.sv
