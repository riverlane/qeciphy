
# SPDX-License-Identifier: None
# Copyright (c) 2024-2025 Riverlane Ltd.
# Original authors: jamesf-rlane, ONDWARAKA


# Search path for included files (may need changing for different simulators)
+incdir+./verif_vip/agents/riv_rdy_vld_source_agent
+incdir+./verif_vip/agents/riv_rdy_vld_source_agent/sequences

// All files to be compiled, in the correct order (bottom-up)
verif_vip/agents/riv_rdy_vld_source_agent/riv_rdy_vld_source_agent_pkg.sv
verif_vip/agents/riv_rdy_vld_source_agent/riv_rdy_vld_source_agent_if.sv
verif_vip/agents/riv_rdy_vld_source_agent/bfms/riv_rdy_vld_source_bfm.sv
verif_vip/agents/riv_rdy_vld_source_agent/bfms/riv_rdy_vld_source_monitor_bfm.sv
