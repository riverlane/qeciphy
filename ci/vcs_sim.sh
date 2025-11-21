#!/bin/bash
set -e 
set -o pipefail

echo "=== QECIPHY Multi-Platform VCS Simulation ==="

echo "Purging modules..."
module purge

echo "Loading Vivado and VCS..."
module load xilinx/vivado/2024.1 
module load synopsys/vcs

# Test all supported platforms
PROFILES=("zcu216" "zcu106" "kasliSoC")

for profile in "${PROFILES[@]}"; do
    echo ""
    echo "--- Testing profile: $profile ---"

    echo "Cleaning previous builds..."
    make distclean
    
    echo "Generating XCI cores for $profile..."
    make generate-xci OPT_PROFILE=$profile OPT_SIM_FILES=true
    
    echo "Running VCS simulation for $profile..."
    make sim OPT_PROFILE=$profile OPT_SIMULATOR=vcs
    
    echo "$profile VCS simulation completed successfully!"
done

echo ""
echo "All platform VCS simulations completed successfully!"