# QECIPHY

**Q**uantum **E**rror **C**orrection **I**nterface **PHY**sical Layer

QECIPHY is a physical layer implementation according to the [QECi (Quantum Error Correction interface) open standard](https://www.riverlane.com/get-qec-ready/qeci) designed for FPGA-to-FPGA communication. Originally designed for quantum error correction systems, QECIPHY is a lightweight IP that exposes a simple AXI4-Stream based interface, significantly simplifying high-speed FPGA-to-FPGA communication for any application.

[![License](https://img.shields.io/badge/License-Custom-blue.svg)](LICENSE)
[![Vivado](https://img.shields.io/badge/Vivado-2024%2B-orange.svg)]()
[![SystemVerilog](https://img.shields.io/badge/HDL-SystemVerilog-green.svg)]()

[![Lint](https://img.shields.io/github/actions/workflow/status/riverlane/qeciphy/regressions.yml?label=Lint&branch=main)](https://github.com/riverlane/qeciphy/actions/workflows/regressions.yml)
[![Simulation](https://img.shields.io/github/actions/workflow/status/riverlane/qeciphy/regressions.yml?label=Simulation&branch=main)](https://github.com/riverlane/qeciphy/actions/workflows/regressions.yml)
[![Synthesis](https://img.shields.io/github/actions/workflow/status/riverlane/qeciphy/regressions.yml?label=Synthesis&branch=main)](https://github.com/riverlane/qeciphy/actions/workflows/regressions.yml)
[![UVM](https://img.shields.io/github/actions/workflow/status/riverlane/qeciphy/regressions.yml?label=UVM&branch=main)](https://github.com/riverlane/qeciphy/actions/workflows/regressions.yml)


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
- **Functionality Verified**: Verified using SV-UVM testbench end-to-end. Formal verification of most modules.
- **Multi-Platform Simulation**: Supports simulation on multiple platforms (XSim, VCS)

> *You only need to send valid data packets from one FPGA and receive valid data packets on the other - no need to add headers, manage link state, or handle physical layer protocols.*

## Quick Start

### Prerequisites

**To use QECIPHY:**
- Vivado 2024.1+: tested with 2024.1 
- Python 3.8+: for build scripts
- Make: for build automation

**Additional tools needed for development:**
- Verilator v5.020: for linting
- Verible v0.0-3430: for formatting
- Git: for version control
- VCS: for simulation (optional)
- Synopsys Verdi: for UVM debug (optional)
- VCFormal: for formal verification (optional)

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

> *And you're done! For detailed integration instructions, please refer to the [Integration Guide](INTEGRATION.md).*

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
    output logic        LINK_READY, // Link ready indicator
    output logic        FAULT_FATAL // Fatal fault indicator
);
```

> *If you are interested in more details about the internal architecture, please refer to the [Architecture Document](docs/architecture.md).*

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
├── uvm/                         # UVM testbench (scoreboards, tests and sequences)
├── verif_vip/                   # UVM agents for all interfaces
├── sva/                         # SystemVerilog assertions and bindings
├── formal/                      # Formal verification harnesses and scripts
├── ci/                          # Continuous integration scripts
├── docs/                        # Documentation files
├── config.json                  # Build configuration (profiles, settings)
├── Makefile                     # Build automation
├── src.f, sim.f, lint.f, uvm.f, sva.f # File lists for different flows
├── lint_waivers.vlt             # Verilator lint waivers
├── CODE_OF_CONDUCT.md           # Code of conduct
├── CONTRIBUTING.md              # Development guidelines
├── INTEGRATION.md               # Integration guide
├── MAINTAINERS.md               # Project maintainers
├── README.md                    # This file
└── LICENSE                      # License information
```

## Complete List of Make Targets

For detailed usage of each make target, please type `make help`.

### Cleaning and Maintenance
```bash
# Clean tool specific artifacts
make clean

# Deep clean: includes clean + removes generated IP and simulation files
make distclean
```

### Linting and Formatting
```bash
# Run Verilator linting
make lint  

# Format SystemVerilog files using Verible
make format
```

### Vendor IP Generation
```bash
# Generate vendor IP cores
make generate-xci OPT_PROFILE=<profile> 

# Generate vendor IP cores along with simulation files
make generate-xci OPT_PROFILE=<profile> OPT_SIM_FILES=true
```

> *Always run `make generate-xci` before `make sim`, `make synth` or `make uvm-sim` to ensure the required vendor IP cores are generated. Specifically if you are simulating not using XSim, ensure to generate the simulation files by setting `OPT_SIM_FILES=true` while generating the XCI cores.*

### Simulation
```bash
# Run XSim simulation (batch mode)
make sim OPT_PROFILE=<profile> OPT_TOOL=xsim

# Run XSim simulation (GUI mode)
make sim OPT_PROFILE=<profile> OPT_TOOL=xsim OPT_MODE=gui

# Run VCS simulation (batch mode)
make sim OPT_PROFILE=<profile> OPT_TOOL=vcs

# Run VCS simulation (GUI mode)
make sim OPT_PROFILE=<profile> OPT_TOOL=vcs OPT_MODE=gui
```

> *If you are interested to learn more about multi-platform simulation support, please refer to the [Multi-Platform Simulation Guide](docs/multi_platform_simulation.md).*

### Synthesis
```bash
# Run synthesis using Vivado (batch mode)
make synth OPT_PROFILE=<profile>

# Run synthesis using Vivado (GUI mode)
make synth OPT_PROFILE=<profile> OPT_MODE=gui
```

### UVM Testing
```bash
# Run UVM test using VCS in batch mode
make uvm-sim OPT_TEST=<test> OPT_PROFILE=<profile>

# Run UVM test with VCS in GUI mode
make uvm-sim OPT_TEST=<test> OPT_PROFILE=<profile> OPT_MODE=gui

# Run UVM test in batch mode with coverage database
make uvm-sim OPT_TEST=<test> OPT_PROFILE=<profile> OPT_MODE=cov

# Run UVM test with optional test args
make uvm-sim OPT_TEST=<test> OPT_PROFILE=<profile> OPT_ARGS=+DUT_XFERS=20000
```

> *For more details about the UVM testbench architecture and usage instructions, please refer to the [UVM Simulation Guide](docs/UVM_Simulation.md).*

### Formal Verification
```bash
# Run formal verification using VCFormal
make formal OPT_TOP=<module_name>

# Run VCFormal with GUI
make formal OPT_TOP=<module_name> OPT_MODE=gui
```

> *If you are a desiger interested in using the formal verification framework in this repo, please refer to the [Formal Verification Guide](docs/formal_verification_guide.md).*

## Performance

| Metric | GTX (7-series)  | GTH (UltraScale) | GTY (UltraScale+) |
|--------|----------------|----------------------|----------------------|
| **Latency** | ~220ns | ~190ns |~195ns |
| **LUT** | 1372 | 1230 | 1230 |
| **FF** | 1229 | 1156 | 1156 |

*Measured at 12.5 Gbps line rate. Performance varies by platform and configuration.*

## Contributing

We welcome contributions from the community! Please refer to the [Contribution Guide](CONTRIBUTING.md) for details on how to contribute.

## License

Please see the [LICENSE](LICENSE) file for license details.

## Support

- **Issues**: [GitHub Issues](https://github.com/riverlane/qeciphy/issues)
