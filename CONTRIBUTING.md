# Contributing to QECIPHY

Thank you for your interest in contributing to QECIPHY! This document provides guidelines for contributing to the project.

## Code of Conduct

This project adheres to the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md). By participating, you are expected to uphold this code.

## Getting Started

### Prerequisites

Before contributing, ensure you have:
- **Vivado 2024+** (tested with 2024.1)
- **Python 3.8+** for build scripts
- **Make** for build automation
- **Verilator v5.020** for linting
- **Verible v0.0-3430** for formatting
- **Git** for version control

### Development Environment Setup

1. **Clone the repository:**
   ```bash
   git clone https://github.com/riverlane/qeciphy.git
   cd qeciphy
   ```

2. **Generate required IP cores and test synthesis:**
   ```bash
   make generate-xci OPT_PROFILE=zcu216
   make synth OPT_PROFILE=zcu216
   ```

3. **Test simulation flow:**
   ```bash
   make generate-xci OPT_PROFILE=zcu216
   make sim OPT_PROFILE=zcu216
   ```

## Project Structure

```
qeciphy/
├── src/                    # Core SystemVerilog sources
├── src.f                   # Source file list
├── tb/                     # Testbenches
├── sim.f                   # Simulation file list
├── lint.f                  # Linting file list
├── lib/                    # Submodules (async_fifo, synchronizer_2ff)
├── lint_stubs/             # Lint stubs for vendor IP
├── example_designs/        # Integration examples
├── vendors/xilinx/         # Vendor IP generation scripts
├── scripts/                # Build automation scripts
├── run/                    # Build outputs (generated)
├── config.json             # Profile configurations
└── Makefile               # Build system
```

## How to Contribute

### Reporting Issues

When reporting issues, please include:
- **Hardware platform** (e.g., ZCU106, ZCU216, KasliSoC)
- **Vivado version**
- **Profile used** (`zcu216`, `zcu106`, `kasliSoC`)
- **Complete error messages**
- **Steps to reproduce**

### Submitting Changes

1. **Create a feature branch:**
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make your changes** following the coding standards below

3. **Test your changes:**
   ```bash
   # Clean previous artifacts
   make clean
   
   # Format and lint code
   make format
   make lint
   
   # Test simulation for all profiles
   make generate-xci OPT_PROFILE=zcu216
   make sim OPT_PROFILE=zcu216
   
   make generate-xci OPT_PROFILE=zcu106
   make sim OPT_PROFILE=zcu106
   
   make generate-xci OPT_PROFILE=kasliSoC
   make sim OPT_PROFILE=kasliSoC
   
   # Test synthesis for at least one profile
   make synth OPT_PROFILE=zcu216
   ```

4. **Commit your changes:**
   ```bash
   git add .
   git commit -m "feat: add your feature description"
   ```

5. **Push and create a pull request**

## Coding Standards

### SystemVerilog Guidelines

- **Naming Convention:**
  - Modules: `snake_case` (e.g., `qeciphy_controller`)
  - Signals: `snake_case` (e.g., `rx_data_valid`)
  - Parameters: `UPPER_CASE` (e.g., `DATA_WIDTH`)
  - Constants: `UPPER_CASE` (e.g., `CRC_POLYNOMIAL`)

- **File Organization:**
  - One module per file
  - Filename matches module name
  - Use `.sv` extension for SystemVerilog

### Example Module Template:

```systemverilog
// SPDX-License-Identifier: BSD-3-Clause

module qeciphy_example #(
    parameter int DATA_WIDTH = 64,
    parameter int ADDR_WIDTH = 8
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic [DATA_WIDTH-1:0]   data_in,
    input  logic                    valid_in,
    output logic [DATA_WIDTH-1:0]   data_out,
    output logic                    valid_out
);

    // Implementation here

endmodule
```

## Available Make Targets

```bash
make clean                           # Clean build artifacts (no profile required)
make lint                            # Run Verilator linting (no profile required)
make format                          # Format all .sv files (no profile required)
make generate-xci OPT_PROFILE=<profile>  # Generate XCI files (requires device.part + variant)
make sim OPT_PROFILE=<profile>       # Run simulation (requires device.part + variant)
make synth OPT_PROFILE=<profile>     # Run synthesis (requires all synth fields)
```

**Profile Requirements:**
- **`make clean/lint/format`**: No profile or config.json fields required
- **`make generate-xci/sim`**: Requires `device.part` and `variant` fields in profile
- **`make synth`**: Requires complete `synth` section with all sub-fields in profile

**Important:** Always run `make generate-xci` before `make sim` or `make synth` to ensure required IP cores are available.

## Adding New Hardware Support

To add support for a new hardware platform, you need to provide different config.json fields depending on which Make targets you want to support:

**For `make generate-xci` and `make sim` support:**
- Minimum required fields: `device.part` and `variant`

**For `make synth` support:**
- Required fields: All fields shown below (complete profile)

1. **Add profile to `config.json`:**
   ```json
   "your_platform": {
       "device": {
           "part": "your-fpga-part-number",
           "vendor": "xilinx"
       },
       "board": "board-part-identifier",
       "variant": "GTX|GTH|GTY",
       "synth": {
           "top": "qeciphy_syn_wrapper",
           "filelists": [
               "example_designs/your_platform/src.f"
           ],
           "constraints": [
               "example_designs/your_platform/syn/constraints.xdc"
           ],
           "pre_setup_hooks": [
               "example_designs/vendors/xilinx/qeciphy_rx_ila.tcl",
               "example_designs/vendors/xilinx/qeciphy_vio.tcl"
           ]
       }
   }
   ```

   **Field Descriptions:**
   - **`device.part`** (required): Full FPGA part number including package and speed grade
     - Example: `"xczu49dr-ffvf1760-2-e"` for ZCU216
     - Example: `"xczu7ev-ffvc1156-2-e"` for ZCU106
     - Example: `"xc7z030ffg676-3"` for KasliSoC
   
   - **`device.vendor`** (required): FPGA vendor, currently only `"xilinx"` supported
   
   - **`board`** (optional): Vivado board part identifier for board-specific constraints
     - Example: `"xilinx.com:zcu216:part0:2.0"`
     - Example: `"xilinx.com:zcu106:part0:2.6"`
     - Omit if using custom board or no board files available
   
   - **`variant`** (required): Transceiver type used by this platform
     - `"GTX"`: 7-series FPGAs (e.g., Kintex-7, Artix-7)
     - `"GTH"`: UltraScale/UltraScale+ FPGAs with GTH transceivers
     - `"GTY"`: UltraScale+ FPGAs with GTY transceivers
   
   - **`synth.top`** (required): Top-level synthesis module name
     - Usually `"qeciphy_syn_wrapper"` for integration examples
   
   - **`synth.filelists`** (required): Array of file list paths containing source files
     - Each `.f` file contains SystemVerilog source file paths
     - Example: `["example_designs/your_platform/src.f"]`
   
   - **`synth.constraints`** (required): Array of XDC constraint file paths
     - Timing constraints, pin assignments, clock definitions
     - Example: `["example_designs/your_platform/syn/constraints.xdc"]`
   
   - **`synth.pre_setup_hooks`** (optional): Array of TCL scripts to run during synthesis
     - Scripts to generate IP cores (ILA, VIO, etc.)
     - Run before project setup in Vivado
     - Common hooks: ILA for debugging, VIO for control signals

2. **Create example design:**
   - Add directory under `example_designs/your_platform/`
   - Include synthesis wrapper and constraints
   - Add `src.f`

3. **Test thoroughly:**
   - Verify synthesis passes
   - Check timing closure
   - Validate transceiver configuration

## Documentation

When contributing, please update relevant documentation:

- Update `README.md` if adding new features
- Add entries to `docs/variants.md` for new platform support
- Document any new build targets in `docs/integration.md`
- Update `docs/filelists.md` for new source files

## License

By contributing to QECIPHY, you agree that your contributions will be licensed under the project's license (BSD-3-Clause upon public release).

## Getting Help

- **Issues:** Use GitHub Issues for bugs and feature requests
- **Discussions:** Use GitHub Discussions for questions and ideas
- **Maintainers:** See [MAINTAINERS.md](MAINTAINERS.md) for contact information

Thank you for contributing to QECIPHY!