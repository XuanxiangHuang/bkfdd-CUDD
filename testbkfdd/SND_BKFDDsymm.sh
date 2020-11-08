#!/bin/bash

################################################################################
# Executes command with a timeout
# Params:
#   $1 timeout in seconds
#   $2 command
# Returns 1 if timed out 0 otherwise
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
program="./bkfdds -autodyn -automethod bkfddsymm -reordering bkfdd-symm-mix -drop Benchmark/"
arguments="-davioexist 100"
cat $test_cases_file | while read oneline
do
    timeout 3600 "$program$oneline $arguments -dumpfile BKFDD_symm/$oneline -dumpblif" >> SND_BKFDDsymm.txt
done

test_cases_file="BenchmarkList_EPFL.txt"
program="./bkfdds -autodyn -automethod bkfddsymm -reordering bkfdd-symm-mix -drop Benchmark/"
arguments="-davioexist 50"
cat $test_cases_file | while read oneline
do
if [ "$oneline" == "sin.blif" ] ; then
		arguments="-davioexist 15"
elif [ "$oneline" == "max.blif" ] ; then
		arguments="-davioexist 10 -choosenew 9996 -choosedav 9755 -choosefail 150"
elif [ "$oneline" == "voter.blif" ] ; then
		arguments="-davioexist 5 -choosenew 9900 -choosedav 9700 -choosefail 100"
fi
    timeout 3600 "$program$oneline $arguments -dumpfile BKFDD_symm/$oneline -dumpblif" >> SND_BKFDDsymm.txt
done

test_cases_file="BenchmarkList3.txt"
program="./bkfdds -autodyn -automethod bkfddsymm -reordering bkfdd-symm-mix -drop Benchmark/"
arguments="-davioexist 50"
cat $test_cases_file | while read oneline
do
if [ "$oneline" == "ITC_b15.blif" ] ; then
		arguments="-davioexist 30 -choosedav 9997"
elif [ "$oneline" == "ITC_b20.blif" ] ; then
		arguments="-davioexist 30 -choosenew 9997 -choosedav 9948 -choosefail 100"
fi
    timeout 3600 "$program$oneline $arguments -dumpfile BKFDD_symm/$oneline -dumpblif" >> SND_BKFDDsymm.txt
done

exit 0
