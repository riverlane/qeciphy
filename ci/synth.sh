#!/bin/bash
set -e
set -o pipefail

echo "=== QECIPHY Multi-Platform Synthesis ==="

echo "Purging modules..."
module purge

echo "Loading Vivado..."
module load xilinx/vivado

# Test all supported platforms
PROFILES=("zcu216" "zcu106" "kasliSoC")

for profile in "${PROFILES[@]}"; do
    echo ""
    echo "--- Synthesizing profile: $profile ---"

    echo "Cleaning previous builds..."
    make clean
    
    echo "Generating XCI cores for $profile..."
    make generate-xci OPT_PROFILE=$profile
    
    echo "Running synthesis for $profile..."
    make synth OPT_PROFILE=$profile
    
    echo "$profile synthesis completed successfully!"
done

echo ""
echo "All platform synthesis completed successfully!"
