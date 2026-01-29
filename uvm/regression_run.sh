
#!/bin/bash
mkdir -p uvm_regression_logs
SUMMARY_FILE="uvm_regression_logs/summary.txt"
: > "$SUMMARY_FILE"  # Empty the summary file at start
INPUT_FILE="uvm/regression_list.txt"
PROFILES=("zcu216" "zcu106" "kasliSoC")
# Mapping function for technology type
get_tech_type() {
    local profile="$1"
    case "$profile" in
        zcu216)
            echo "GTY"
            ;;
        zcu106)
            echo "GTH"
            ;;
        kasliSoC)
            echo "GTX"
            ;;
        *)
            echo "UNKNOWN"
            ;;
    esac
}
for profile in "${PROFILES[@]}"; do
    echo "Cleaning previous builds..."
    make distclean
    
    echo "Generating XCI cores for $profile..."
    make generate-xci OPT_PROFILE=$profile OPT_SIM_FILES=true

    make uvm-vcs-compile-sim OPT_PROFILE=$profile
    PASS=0
    FAIL=0
    while IFS=',' read -r TEST_NAME OPT_ARGS; do
        # Construct from TEST_NAME (replace _test with _uvmtb)
        OPT_TEST="${TEST_NAME/_test}"
        
        # Combine all arguments (everything after TEST_NAME)
        # OPT_ARGS already contains multiple +args separated by commas
        # Replace commas with spaces for proper passing
        OPT_ARGS_FORMATTED=$(echo "$OPT_ARGS" | tr ',' ' ')
        
        # Generate random seed
        SEED=$RANDOM
        
        echo "Running: OPT_TEST=$TEST_NAME 
                       OPT_ARGS=\"$OPT_ARGS_FORMATTED\"  
                       OPT_SEED=$SEED 
                       LOG = ${TEST_NAME}_${SEED}_$profile.log "
        # Execute the command
        ./simv -q OPT_ARGS=$OPT_ARGS_FORMATTED +UVM_VERBOSITY=UVM_LOW +UVM_TESTNAME=$TEST_NAME -l uvm_regression_logs/${TEST_NAME}_${SEED}_$profile.log +ntb_random_seed=${SEED} -cm line+cond+tgl+fsm+branch+assert +enable_coverage=1 -cm_dir coverage/${TEST_NAME}_${SEED}_$profile_cov.vdb[...] > /dev/null 2>&1
        # check the log for pass/fail
         if [[ ! -f "uvm_regression_logs/${TEST_NAME}_${SEED}_$profile.log" ]]; then
            echo "Log file not found! Test $TEST_NAME may have failed to run."
            exit 1
         fi

         if grep -q "***FAILED***" "uvm_regression_logs/${TEST_NAME}_${SEED}_$profile.log"; then
             echo "${TEST_NAME}_${SEED}_$profile failed"
             FAIL=$((FAIL+1))
         else
             echo "${TEST_NAME}_${SEED}_$profile passed"
                PASS=$((PASS+1))
         fi
    done < "$INPUT_FILE"
    # Get the technology type for the profile
    TECH_TYPE=$(get_tech_type "$profile")
    f [[ $FAIL -gt 0 ]]; then
        EMOJI="🚨😞🚨"
        HEADER="Sad Regression Summary: \`$profile\`"
        IMG_URL="https://media.giphy.com/media/ARSp9T7wwxNcs/giphy.gif"  # Sad Pikachu GIF
    else
        EMOJI="🎉"
        HEADER="Regression Summary: \`$profile\`"
        IMG_URL="https://media.giphy.com/media/od5H3PmEG5EVq/giphy.gif"  # Party GIF
    fi

    {
        echo ""
        echo "<div align='center'>"
        echo ""
        echo "# $EMOJI **$HEADER** $EMOJI"
        echo ""
        echo "<img src='https://img.shields.io/badge/TECHNOLOGY-$TECH_TYPE-blueviolet?style=for-the-badge&logo=github' alt='Tech Type Badge'>"
        echo ""
        echo "</div>"
        echo ""
        echo "---"
        echo ""
        echo "|  Test Run  |  Result  |"
        echo "|:----------:|:--------:|"
        for result in "${PROFILE_RESULTS[@]}"; do
            echo "$result"
        done
        echo ""
        echo "---"
        echo ""
        echo "<div align='center'>"
        echo "<img src='https://img.shields.io/badge/TOTAL--PASSED-$PASS-brightgreen?style=for-the-badge&logo=github'>&nbsp;"
        echo "<img src='https://img.shields.io/badge/TOTAL--FAILED-$FAIL-red?style=for-the-badge&logo=github'>"
        echo "</div>"
        echo ""
        echo "<div align='center'>"
        echo "![Sad Pikachu]($IMG_URL)"
        echo "</div>"
        echo ""
        echo "<hr style='border: 1px dashed orange'>"
        echo ""
    } >> "$SUMMARY_FILE"
    cat "$SUMMARY_FILE"
    echo " $profile:FAILED_TESTS: $FAIL
          PASSED_TESTS: $PASS"
done
