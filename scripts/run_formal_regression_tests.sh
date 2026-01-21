#!/bin/bash
set -e
set -o pipefail

echo "=== QECIPHY Formal Verification Regression ==="

echo "Purging modules..."
module purge

echo "Loading VC Formal..."
module load synopsys/vcformal

echo "Discovering formal verification harnesses..."

# Find all harness files and extract module names
MODULES=()
for harness in formal/harness/*_harness.sv; do
    if [ -f "$harness" ]; then
        # Extract module name: remove path, remove .sv extension, remove _harness suffix
        basename_harness=$(basename "$harness" .sv)
        module_name=${basename_harness%_harness}
        MODULES+=("$module_name")
    fi
done

if [ ${#MODULES[@]} -eq 0 ]; then
    echo "No harness files found in formal/harness directory"
    exit 1
fi

echo "Found ${#MODULES[@]} harnesses:"
for module in "${MODULES[@]}"; do
    echo "  - $module"
done

# Clean pre-existing artifacts
make clean

# Create results directory
mkdir -p run/formal/results/

# Run formal verification for each module
for module in "${MODULES[@]}"; do
    echo ""
    echo "--- Running formal verification for: $module ---"
    
    make formal OPT_TOP="$module"
    
    # Copy results to centralized location
    if [ -f "run/formal/$module/results.txt" ]; then
        cp "run/formal/$module/results.txt" "run/formal/results/${module}_results.txt"
        echo "Results saved to run/formal/results/${module}_results.txt"
    else
        echo "Error: Results file not found for $module"
        exit 1
    fi
    
    echo "$module formal verification completed successfully!"
done

echo ""
echo "All formal verification tests completed successfully!"