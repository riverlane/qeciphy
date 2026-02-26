# Multi-Platform Simulation Support

QECIPHY supports multiple simulation platforms to accommodate different development workflows and preferences. This document provides comprehensive guidance for using both Xilinx XSim and Synopsys VCS simulators.

## Supported Simulators

| Simulator | Version | Status |
|-----------|---------|--------|
| **Xilinx XSim** | 2024.1+ | ✅ Default |
| **Synopsys VCS** | U-2023.03+ | ✅ Supported |

## Quick Start

**Prerequisites**: Ensure `vivado` and `vcs` commands are available in your system PATH or through environment modules before running simulations.

### XSim (Default)
```bash
# Render design for your platform
make render-design OPT_PROFILE=zcu216

# Run simulation
make sim OPT_PROFILE=zcu216 OPT_TOOL=xsim # Non-GUI mode
# make sim OPT_PROFILE=zcu216 OPT_TOOL=xsim OPT_MODE=gui # GUI mode
```

### VCS
```bash
# Render design for your platform with corresponding simulation files
make render-design OPT_PROFILE=zcu216 OPT_SIM_FILES=true

# Run VCS simulation
make sim OPT_PROFILE=zcu216 OPT_TOOL=vcs # Non-GUI mode
# make sim OPT_PROFILE=zcu216 OPT_TOOL=vcs OPT_MODE=gui # GUI mode
```

## IP Generation and Simulation Files

### Xilinx IP Cores

QECIPHY uses several Xilinx IP cores that require generation:

| IP Core | Purpose | GT Types |
|---------|---------|----------|
| `qeciphy_gtx_transceiver` | GTX transceiver wrapper | GTX (7-series) |
| `qeciphy_gth_transceiver` | GTH transceiver wrapper | GTH (UltraScale) |
| `qeciphy_gty_transceiver` | GTY transceiver wrapper | GTY (UltraScale+) |
| `qeciphy_clk_mmcm` | Clock generation | GTX (7-series) |

### Simulation File Generation

When `OPT_SIM_FILES=true` is specified, the build system:

1. Generates vendor IP cores (.xci files)
2. Exports simulation models to `tb/generated_sim_files/`
3. Creates `generated_sim.f` file list for simulator consumption

```bash
# Render design along with simulation files
make render-design OPT_PROFILE=<profile> OPT_SIM_FILES=true

# Generated files structure
tb/generated_sim_files/
├── <ip_core_name>/             # One or more IP cores (e.g., qeciphy_gty_transceiver)
│   ├── *.v                     
│   ├── *.sv                    
│   ├── *.vhd, *.vhdl           
│   └── includes/               # Include files for this IP
│       └── *.vh, *.svh         
└── generated_sim.f             # File list for simulator

# Profile-specific IP cores generated:
# - kasliSoC: qeciphy_clk_mmcm + qeciphy_gtx_transceiver
# - zcu106:   qeciphy_gth_transceiver  
# - zcu216:   qeciphy_gty_transceiver
```