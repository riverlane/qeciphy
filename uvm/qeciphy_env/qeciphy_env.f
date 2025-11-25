# SPDX-License-Identifier: None
# Copyright (c) 2024-2025 Riverlane Ltd.
# Original authors: jamesf-rlane, ONDWARAKA

# Search path for included files (may need changing for different simulators)
+incdir+./uvm/qeciphy_env
+incdir+./uvm/qeciphy_env/sequences
+incdir+./uvm/qeciphy_env/sequences/utils
+incdir+./uvm/qeciphy_env/coverage_collectors
+incdir+./uvm/qeciphy_env/scoreboards

# Add +defines etc. here

# Add env-wide package / define files to be compiled here

# Add structural models / interfaces to be compiled here
uvm/qeciphy_env/qeciphy_env_miscio_if.sv

# UVM files
uvm/qeciphy_env/qeciphy_env_pkg.sv

