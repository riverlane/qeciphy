# QECIPHY

**Q**uantum **E**rror **C**orrection **I**nterface **PHY**sical Layer

QECIPHY is a physical layer implementation for FPGA-to-FPGA communication designed according to the QECi (Quantum Error Correction interface) open standard. Originally designed for quantum error correction systems, QECIPHY is a lightweight IP that exposes a simple AXI4-Stream interface, significantly simplifying high-speed FPGA-to-FPGA communications for any application.

[![License](https://img.shields.io/badge/License-BSD--3--Clause-blue.svg)](LICENSE)
[![Vivado](https://img.shields.io/badge/Vivado-2024%2B-orange.svg)]()
[![SystemVerilog](https://img.shields.io/badge/HDL-SystemVerilog-green.svg)]()

## Key Features

- **Simple Interface**: AXI4-Stream interface hides all physical layer complexity
- **Universal Compatibility**: Supports any Xilinx FPGA with GTX, GTH, or GTY transceivers
- **Performance**: 12.5 Gbps data rate with ~150-200ns latency
- **Transparent Operation**: Handles clock recovery, frame alignment, CRC checks automatically
- **No Protocol Overhead**: Send valid packets on one end, receive valid packets on the other
- **Open Standard**: Based on QECi specification - an open standard

## What QECIPHY Does For You

QECIPHY deals with all the low-level physical layer details:
- **Clock Recovery**: Recovers clock from incoming data stream
- **Frame Alignment**: Automatic byte and word boundary detection
- **Error Detection**: CRC-16 for data packets, CRC-8 for control packets
- **Link Management**: Automatic link training and status monitoring
- **Power Management**: Optional power state control with P-channel interface

This means you only need to send valid data packets from one FPGA and receive valid data packets on the other - no need to add headers, manage link state, or handle physical layer protocols.

## Quick Start

### Prerequisites

**To use QECIPHY:**
- Vivado 2024+: tested with 2024.1 
- Python 3.8+: for build scripts
- Make: for build automation

**For development:**
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
make generate-xci OPT_PROFILE=zcu216    # GTY transceivers
# make generate-xci OPT_PROFILE=zcu106   # GTH transceivers  
# make generate-xci OPT_PROFILE=kasliSoC # GTX transceivers

# Run your first simulation
make sim OPT_PROFILE=zcu216

# Run synthesis
make synth OPT_PROFILE=zcu216
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

## Performance (Placeholder)

| Metric | GTX (7-series) | GTH/GTY (UltraScale+) |
|--------|----------------|----------------------|
| **Latency** | ~200ns | ~150ns |
| **Resource Usage** | ~5K LUTs | ~6K LUTs |

*Performance varies by platform and configuration*

## Integration

If you want to integrate QECIPHY into your design, see [docs/integration.md](docs/integration.md).

## Development

If you want to contribute to QECIPHY development, see [CONTRIBUTING.md](CONTRIBUTING.md).

## Documentation

- **[Integration Guide](docs/integration.md)** - How to use QECIPHY in your design
- **[QECi Specification](https://www.riverlane.com/get-qec-ready/qeci)** - Physical layer specification (LaTeX source)
- **[Contributing Guide](CONTRIBUTING.md)** - Development and contribution guidelines

## License

This repository is not yet open-sourced. The final BSD-3-Clause license will be added prior to public release.

## Support

- **Issues**: [GitHub Issues](https://github.com/riverlane/qeciphy/issues)
