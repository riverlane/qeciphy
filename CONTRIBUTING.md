# Contributing to QECIPHY

Thank you for your interest in contributing to QECIPHY! 

Please ensure you have read [README.md](README.md) and [INTEGRATION.md](INTEGRATION.md) before contributing.

## Code of Conduct

This project adheres to the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md). By participating, you are expected to uphold this code.

## Quick Setup Test

```bash
# Verify development tools work
make clean
make lint
make format
make generate-xci OPT_PROFILE=zcu216
make sim OPT_PROFILE=zcu216
make synth OPT_PROFILE=zcu216
```

## How to Contribute

### Reporting Issues

Include in your issue report:
- Profile used 
- Vivado version
- Complete error messages and reproduction steps

### Submitting Changes

1. **Create a feature branch:**
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make your changes** following the coding standards below.

3. **Test your changes:**
   ```bash
   make clean
   make format
   make lint
   make generate-xci OPT_PROFILE=zcu216
   make sim OPT_PROFILE=zcu216
   make synth OPT_PROFILE=zcu216
   # Test other profiles as needed
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

### Example Module Template:

```systemverilog
// SPDX-License-Identifier: LicenseRef-LICENSE

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

## Adding New Hardware Support

See [INTEGRATION.md](INTEGRATION.md) for detailed platform configuration. For contributors:

1. Add `config.json` profile with required fields
2. Create example design under `example_designs/your_platform/`
3. Test thoroughly - verify synthesis, timing closure, and successful operation on hardware
4. Update documentation as needed

## Documentation Updates

Update documentation when contributing:

- **README.md** for new features
- **INTEGRATION.md** for new platform support  
- **This file** for new development processes

## License

By contributing to QECIPHY, you agree that your contributions will be licensed under the project's license (see [LICENSE](LICENSE) file).

## Getting Help

- **Issues:** Use GitHub Issues for bugs and feature requests
- **Maintainers:** See [MAINTAINERS.md](MAINTAINERS.md) for contact information

Thank you for contributing to QECIPHY!