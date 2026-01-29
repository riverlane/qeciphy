
#!/bin/bash
mkdir -p uvm_regression_logs
SUMMARY_FILE="uvm_regression_logs/summary.md"
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
    PROFILE_RESULTS=()
    while IFS=',' read -r TEST_NAME OPT_ARGS; do
        # Construct from TEST_NAME (replace _test with _uvmtb)
        OPT_TEST="${TEST_NAME/_test}"
        
        # Combine all arguments (everything after TEST_NAME)
        # OPT_ARGS already contains multiple +args separated by commas
        # Replace commas with spaces for proper passing
        OPT_ARGS_FORMATTED=$(echo "$OPT_ARGS" | tr ',' ' ')
        
        # Generate random seed
        SEED=$RANDOM
        LOG_FILE="${TEST_NAME}_${SEED}_$profile.log"
        LOG_PATH="uvm_regression_logs/$LOG_FILE"
        
        echo "Running: OPT_TEST=$TEST_NAME 
                       OPT_ARGS=\"$OPT_ARGS_FORMATTED\"  
                       OPT_SEED=$SEED 
                       LOG = $LOG_FILE "
        # Execute the command
        ./simv -q OPT_ARGS=$OPT_ARGS_FORMATTED +UVM_VERBOSITY=UVM_LOW +UVM_TESTNAME=$TEST_NAME -l $LOG_PATH +ntb_random_seed=${SEED} -cm line+cond+tgl+fsm+branch+assert +enable_coverage=1 -cm_dir coverage/${TEST_NAME}_${SEED}_$profile_cov.vdb[...] > /dev/null 2>&1
        # check the log for pass/fail
        if [[ ! -f "$LOG_PATH" ]]; then
            echo "Log file not found! Test $TEST_NAME may have failed to run."
            exit 1
        fi

        if grep -q "***FAILED***" "$LOG_PATH"; then
            echo "${TEST_NAME}_${SEED}_$profile failed"
            PROFILE_RESULTS+=("| $TEST_NAME | FAILED |")
            FAIL=$((FAIL+1))
        else
            echo "${TEST_NAME}_${SEED}_$profile passed"
            PROFILE_RESULTS+=("| $TEST_NAME | PASSED |")
            PASS=$((PASS+1))
        fi
    done < "$INPUT_FILE"
    # Fun emoji or ASCII-style header
    if [ "$FAIL" -eq 0 ]; then
        STATUS_EMOJI="🎉"
        MSG="All tests passed! Great job! 🚀"
    else
        STATUS_EMOJI="💥"
        MSG="Some tests failed! Don't give up! 😤"
    fi

    TECH_TYPE=$(get_tech_type "$profile")

    # Write profile summary (Markdown) to the file
    {
        echo "## Profile:  \`$TECH_TYPE\`"
        echo ""
        echo "### Test Results"
        echo ""
        echo "| Test name | Status |"
        echo "|-----------|--------|"
        for result in "${PROFILE_RESULTS[@]}"; do
            echo "$result"
        done
        echo ""
        echo "**Total Passed:** $PASS  "
        echo "**Total Failed:** $FAIL"
        echo ""
        echo "### $STATUS_EMOJI $MSG"
        echo ""
        echo "---"
        echo ""
    } >> "$SUMMARY_FILE"

    cat "$SUMMARY_FILE"
    echo " $profile:FAILED_TESTS: $FAIL
          PASSED_TESTS: $PASS"
done
