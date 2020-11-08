#!/bin/bash

################################################################################
# Executes command with a timeout
# Params:
#   $1 timeout in seconds
#   $2 command
# Returns 1 if timed out 0 otherwise
#
#	enable parameter "-autodyn"
#
timeout() {

    time=$1

    # start the command in a subshell to avoid problem with pipes
    # (spawn accepts one command)
    command="/bin/sh -c \"$2\""

    expect -c "set echo \"-noecho\"; set timeout $time; spawn -noecho $command; expect timeout { exit 1 } eof { exit 0 }"    

    if [ $? = 1 ] ; then
        echo "Timeout after ${time} seconds"
    fi

}

test_cases_file="BenchmarkList.txt"
program="./bkfdds -sdmode -autodyn -automethod bkfddgroup -reordering bkfdd-group-mix -drop -groupcheck bkfcheck2 Benchmark/"
cat $test_cases_file | while read oneline
do
    timeout 3600 "$program$oneline $arguments -dumpfile BKFDD_extgroup/$oneline -dumpblif" >> SD_BKFDDextgroup.txt
done

test_cases_file="BenchmarkList_EPFL.txt"
program="./bkfdds -sdmode -autodyn -automethod bkfddgroup -reordering bkfdd-group-mix -drop -groupcheck bkfcheck2 Benchmark/"
cat $test_cases_file | while read oneline
do
    timeout 3600 "$program$oneline $arguments -dumpfile BKFDD_extgroup/$oneline -dumpblif" >> SD_BKFDDextgroup.txt
done

test_cases_file="BenchmarkList3.txt"
program="./bkfdds -sdmode -autodyn -automethod bkfddgroup -reordering bkfdd-group-mix -drop -groupcheck bkfcheck2 Benchmark/"
cat $test_cases_file | while read oneline
do
    timeout 3600 "$program$oneline $arguments -dumpfile BKFDD_extgroup/$oneline -dumpblif" >> SD_BKFDDextgroup.txt
done

exit 0
