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
# Generate IP cores
make generate-xci OPT_PROFILE=zcu216

# Run simulation
make sim OPT_PROFILE=zcu216 # Non-GUI mode
make sim OPT_PROFILE=zcu216 OPT_MODE=gui # GUI mode
```

### VCS
```bash
# Generate IP cores with simulation files
make generate-xci OPT_PROFILE=zcu216 OPT_SIM_FILES=true

# Run VCS simulation
make sim OPT_PROFILE=zcu216 OPT_SIMULATOR=vcs # Non-GUI mode
make sim OPT_PROFILE=zcu216 OPT_SIMULATOR=vcs OPT_MODE=gui # GUI mode
```

## IP Generation and Simulation Files

### Xilinx IP Cores

QECIPHY uses several Xilinx IP cores that require generation:

| IP Core | Purpose | GT Types |
|---------|---------|----------|
| `qeciphy_gtx_transceiver` | GTX transceiver wrapper | GTX (7-series) |
| `qeciphy_gth_transceiver` | GTH transceiver wrapper | GTH (UltraScale) |
| `qeciphy_gty_transceiver` | GTY transceiver wrapper | GTY (UltraScale+) |
| `qeciphy_clk_mmcm` | Clock generation (GTX only) | GTX (7-series) |

### Simulation File Generation

When `OPT_SIM_FILES=true` is specified, the build system:

1. Generates IP cores (.xci files)
2. Exports simulation models to `tb/generated_sim_files/`
3. Creates `generated_sim.f` file list for simulator consumption

```bash
# Generate IP with simulation files
make generate-xci OPT_PROFILE=zcu216 OPT_SIM_FILES=true

# Generated files structure for zcu216
tb/generated_sim_files/
└── qeciphy_gty_transceiver/     # GTY transceiver
    ├── *.v                     
    └── *.vhd                   
generated_sim.f                 # File list for simulator

# Generated files structure for zcu106
tb/generated_sim_files/
└── qeciphy_gth_transceiver/     # GTH transceiver
    ├── *.v                     
    └── *.vhd                   
generated_sim.f                 # File list for simulator

# Generated files structure for kasliSoC
tb/generated_sim_files/
├── qeciphy_clk_mmcm/           # Clock MMCM (GTX only)
│   ├── *.v                     
│   └── *.vhd                   
└── qeciphy_gtx_transceiver/    # GTX transceiver
    ├── *.v                     
    └── *.vhd                   
generated_sim.f                 # File list for simulator
```