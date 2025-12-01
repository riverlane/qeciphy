
#!/bin/bash
mkdir -p uvm_regression_logs
INPUT_FILE="uvm/regression_list.txt"
PROFILES=("zcu216" "zcu106" "kasliSoC")
FAIL=0
PASS=0
for profile in "${PROFILES[@]}"; do
    echo "Cleaning previous builds..."
    make distclean
    
    echo "Generating XCI cores for $profile..."
    make generate-xci OPT_PROFILE=$profile OPT_SIM_FILES=true

    make uvm_compile_sim OPT_TOP=qeciphy_uvmtb OPT_PROFILE=$profile
    while IFS=',' read -r TEST_NAME OPT_ARGS; do
        # Construct OPT_TOP from TEST_NAME (replace _test with _uvmtb)
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
        ./simv -q OPT_ARGS=$OPT_ARGS_FORMATTED +UVM_VERBOSITY=UVM_LOW +UVM_TESTNAME=$TEST_NAME -l uvm_regression_logs/${TEST_NAME}_${SEED}_$profile.log +ntb_random_seed=${SEED} -cm line+cond+tgl+fsm+branch+assert +enable_coverage=1 -cm_dir coverage/${TEST_NAME}_${SEED}_$profile_cov.vdb
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
    echo " $profile:FAILED_TESTS: $FAIL
          PASSED_TESTS: $PASS"
done