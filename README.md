# QECIPHY

**Q**uantum **E**rror **C**orrection **I**nterface **PHY**sical Layer

QECIPHY is a physical layer implementation according to the QECi (Quantum Error Correction interface) open standard designed for FPGA-to-FPGA communication. Originally designed for quantum error correction systems, QECIPHY is a lightweight IP that exposes a simple AXI4-Stream based interface, significantly simplifying high-speed FPGA-to-FPGA communication for any application.

[![License](https://img.shields.io/badge/License-Custom-blue.svg)](LICENSE)
[![Vivado](https://img.shields.io/badge/Vivado-2024%2B-orange.svg)]()
[![SystemVerilog](https://img.shields.io/badge/HDL-SystemVerilog-green.svg)]()

[![Lint](https://img.shields.io/github/actions/workflow/status/riverlane/qeciphy/regressions.yml?label=Lint&branch=main)](https://github.com/riverlane/qeciphy/actions/workflows/regressions.yml)
[![Simulation](https://img.shields.io/github/actions/workflow/status/riverlane/qeciphy/regressions.yml?label=Simulation&branch=main)](https://github.com/riverlane/qeciphy/actions/workflows/regressions.yml)
[![Synthesis](https://img.shields.io/github/actions/workflow/status/riverlane/qeciphy/regressions.yml?label=Synthesis&branch=main)](https://github.com/riverlane/qeciphy/actions/workflows/regressions.yml)

## Key Features

- **Simple Interface**: AXI4-Stream interface hides all physical layer complexity
- **Universal Compatibility**: Supports any Xilinx FPGA with GTX, GTH, or GTY transceivers
- **Latency**: ~150-200ns latency at 12.5 Gbps line rate
- **Programmable Line Rate**: Configurable transceiver line rates for different bandwidth requirements
- **Open Standard**: Based on QECi Specification - an open standard
- **Clock Recovery**: Recovers clock from incoming data stream automatically
- **Frame Alignment**: Automatic byte and word boundary detection
- **Error Detection**: CRC-16 for data packets, CRC-8 for control packets
- **Link Management**: Automatic link training and status monitoring
- **Power Management**: Optional power state control with P-channel interface

**Bottom Line:** You only need to send valid data packets from one FPGA and receive valid data packets on the other - no need to add headers, manage link state, or handle physical layer protocols.

## Quick Start

### Prerequisites

**To use QECIPHY:**
- Vivado 2024+: tested with 2024.1 
- Python 3.8+: for build scripts
- Make: for build automation

**Additional tools needed for development:**
- Verilator v5.020: for linting
- Verible v0.0-3430: for formatting
- Git: for version control

### Three-Step Setup

We provide three example profiles for different transceiver types:

```bash
# Clone the repository
git clone https://github.com/riverlane/qeciphy.git
cd qeciphy

# Generate XCI cores for your platform
make generate-xci OPT_PROFILE=zcu216     # GTY transceivers
# make generate-xci OPT_PROFILE=zcu106   # GTH transceivers  
# make generate-xci OPT_PROFILE=kasliSoC # GTX transceivers

# Run your first simulation
make sim OPT_PROFILE=zcu216         # GTY transceivers
# make sim OPT_PROFILE=zcu106       # GTH transceivers
# make sim OPT_PROFILE=kasliSoC     # GTX transceivers

# Run synthesis
make synth OPT_PROFILE=zcu216       # GTY transceivers
# make synth OPT_PROFILE=zcu106     # GTH transceivers
# make synth OPT_PROFILE=kasliSoC   # GTX transceivers
```

## Interface

```systemverilog
module QECIPHY #(
    parameter GT_TYPE = "GTY"  // "GTX", "GTH", or "GTY"
) (
    // Clocks and Reset
    input  logic        RCLK,       // GT Reference clock
    input  logic        FCLK,       // Free running clock
    input  logic        ACLK,       // AXI4-Stream clock
    input  logic        ARSTn,      // Active-low reset
    
    // TX AXI4-Stream Interface
    input  logic [63:0] TX_TDATA,   // TX data
    input  logic        TX_TVALID,  // TX valid
    output logic        TX_TREADY,  // TX ready
    
    // RX AXI4-Stream Interface  
    output logic [63:0] RX_TDATA,   // RX data
    output logic        RX_TVALID,  // RX valid
    input  logic        RX_TREADY,  // RX ready
    
    // Status and Control
    output logic [3:0]  STATUS,     // Link status
    output logic [3:0]  ECODE,      // Error codes
    
    // Power Management
    input  logic        PSTATE,     // Power state request
    input  logic        PREQ,       // Power request
    output logic        PACCEPT,    // Power accept
    output logic        PACTIVE     // Power active
);
```

## Project Structure

```
qeciphy/
├── src/                         # Core QECIPHY SystemVerilog sources
├── tb/                          # Testbench files
├── lib/                         # Self-contained, reusable RTL building blocks
├── example_designs/             # Platform-specific integration examples
├── vendors/                     # Vendor-specific IP generation scripts
├── scripts/                     # Build and utility scripts
├── lint_stubs/                  # Lint placeholder modules for IP cores
├── config.json                  # Build configuration (profiles, settings)
├── Makefile                     # Build automation
├── src.f, sim.f, lint.f         # File lists for different flows
├── CONTRIBUTING.md              # Development guidelines
├── README.md                    # This file
└── LICENSE                      # License information
```

## Complete List of Make Targets

```bash
make clean                                      # Clean tool specific artifacts
make distclean                                  # Deep clean: includes clean + removes generated IP and simulation files
make lint                                       # Run Verilator linting
make format                                     # Format SystemVerilog files
make generate-xci OPT_PROFILE=<profile>         # Generate vendor IP
make generate-xci OPT_PROFILE=<profile> OPT_SIM_FILES=true  # Generate vendor IP and corresponding simulation files
make sim OPT_PROFILE=<profile>                  # Run simulation with XSim (batch mode)
make sim OPT_PROFILE=<profile> OPT_MODE=gui     # Run simulation with XSim (GUI mode)
make sim OPT_PROFILE=<profile> OPT_SIMULATOR=vcs # Run VCS simulation (batch mode)
make sim OPT_PROFILE=<profile> OPT_SIMULATOR=vcs OPT_MODE=gui # Run VCS simulation (GUI mode)
make synth OPT_PROFILE=<profile>                # Run synthesis (batch mode)
make synth OPT_PROFILE=<profile> OPT_MODE=gui   # Run synthesis (GUI mode)
```

**Note:** Always run `make generate-xci` before `make sim` or `make synth`.

## Performance

| Metric | GTX (7-series)  | GTH (UltraScale) | GTY (UltraScale+) |
|--------|----------------|----------------------|----------------------|
| **Latency** | ~220ns | ~190ns |~195ns |
| **LUT** | 1372 | 1230 | 1230 |
| **FF** | 1229 | 1156 | 1156 |

*Measured at 12.5 Gbps line rate. Performance varies by platform and configuration.*

## Important Links

- **[QECi Specification](https://www.riverlane.com/get-qec-ready/qeci)** - Physical layer specification
- **[Integration Guide](INTEGRATION.md)** - How to use QECIPHY in your design
- **[Multi-Platform Simulation](docs/multi_platform_simulation.md)** - VCS and XSim simulation support
- **[Contribution Guide](CONTRIBUTING.md)** - Development and contribution guidelines

## License

Please see the [LICENSE](LICENSE) file for license details.

## Support

- **Issues**: [GitHub Issues](https://github.com/riverlane/qeciphy/issues)
