#!/bin/bash

# this script is invoked as part of CI to verify all packages

scriptDir=$(dirname "$0")

# flag whether this script is currently executed as part of a CI
isCi=$CI

# gobraJar="/gobra/gobra.jar"
gobraJar="/Users/arquintlinard/ETH/PhD/gobra/target/scala-2.13/gobra.jar"
additionalGobraArgs="--module github.com/ModularVerification/ReusableVerificationLibrary --include .verification --z3Exe /Users/arquintlinard/.local/bin/z3 --parallelizeBranches"

if [ $isCi ]; then
    echo -e "\033[0Ksection_start:`date +%s`:verify[collapsed=true]\r\033[0KVerifying packages"
fi
time java -Xss128m -jar $gobraJar --recursive -I $scriptDir $additionalGobraArgs
exitCode=$?
if [ $isCi ]; then
    echo -e "\033[0Ksection_end:`date +%s`:verify\r\033[0K"
fi

# set exit code:
exit $exitCode
