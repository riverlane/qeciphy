#!/bin/bash
set -e 
set -o pipefail

echo "=== QECIPHY Multi-Platform Simulation ==="

echo "Purging modules..."
module purge

echo "Loading Vivado..."
module load xilinx/vivado

# Test all supported platforms
PROFILES=("zcu216" "zcu106" "kasliSoC")

for profile in "${PROFILES[@]}"; do
    echo ""
    echo "--- Testing profile: $profile ---"

    echo "Cleaning previous builds..."
    make distclean
    
    echo "Generating XCI cores for $profile..."
    make generate-xci OPT_PROFILE=$profile
    
    echo "Running simulation for $profile..."
    make sim OPT_PROFILE=$profile
    
    echo "$profile simulation completed successfully!"
done

echo ""
echo "All platform simulations completed successfully!"
