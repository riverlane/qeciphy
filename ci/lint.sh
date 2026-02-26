#!/bin/bash
set -e
set -o pipefail 

echo "=== QECIPHY Linting ==="

echo "Purging modules..."
module purge

echo "Loading Verilator..."
module load verilator/verilator

echo "Loading Vivado..."
module load xilinx/vivado

# Test all supported platforms
PROFILES=("zcu216" "zcu106" "kasliSoC")

for profile in "${PROFILES[@]}"; do
    echo ""
    echo "--- Testing profile: $profile ---"

    echo "Cleaning previous builds..."
    make distclean
    
    echo "Rendering design for $profile..."
    make render-design OPT_PROFILE=$profile
    
    echo "Running lint for $profile..."
    make lint
    
    echo "$profile linting completed successfully!"
done

echo "Linting completed successfully!"
