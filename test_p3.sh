#!/bin/bash

# Check that the test directory and the executable file exist
if [ ! -d "./tests" ]; then
    echo "Error: test directory not found!"
    exit 1
fi

if [ ! -e "./a.out" ]; then
    echo "Error: a.out not found!"
    exit 1
fi

if [ ! -x "./a.out" ]; then
    echo "Error: a.out not executable!"
    exit 1
fi

# Create the output directory
mkdir -p ./output

# Loop through all test files in the test directory
for test_file in $(find ./tests -type f -name "*.txt" | sort); do
    # Get the base name of the test file (without the extension)
    name=$(basename "${test_file%.*}")
    
    # Set the expected output file name
    expected_file=${test_file}.expected
    
    # Set the output file and diff file names
    output_file=./output/${name}.output
    diff_file=./output/${name}.diff
    
    # Run the program with input from the test file and redirect output to the output file
    ./a.out < "${test_file}" > "${output_file}"
    
    # Compare the program output with the expected output and redirect the difference to the diff file
    diff -Bw "${expected_file}" "${output_file}" > "${diff_file}"
    
    # Print the test result
    echo
    if [ -s "${diff_file}" ]; then
        echo "${name}: Output does not match expected:"
        echo "--------------------------------------------------------"
        cat "${diff_file}"
    else
        echo "${name}: OK"
    fi
    echo "========================================================"
    
    # Clean up the output file and diff file
    rm -f "${output_file}"
    rm -f "${diff_file}"
done

# Remove the output directory
rmdir ./output
