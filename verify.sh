#!/bin/bash

# this script is invoked as part of CI to verify all packages

scriptDir=$(dirname "$0")

# flag whether this script is currently executed as part of a CI
isCi=$CI

# create .gobra folder if it does not exist yet:
mkdir -p $scriptDir/.gobra

<<<<<<< HEAD
gobraJar="/gobra/gobra.jar"
additionalGobraArgs="--module github.com/ModularVerification/ReusableVerificationLibrary --include .verification --gobraDirectory $scriptDir/.gobra --parallelizeBranches"

if [ $isCi ]; then
    echo -e "\033[0Ksection_start:`date +%s`:verify[collapsed=true]\r\033[0KVerifying packages"
fi
java -Xss128m -jar $gobraJar --recursive -I $scriptDir $additionalGobraArgs
=======
preArgs="/usr/local/Cellar/openjdk/19.0.2/bin/java"
gobraJar="/Users/hugoqueinnec/Documents/ETH/Thesis/gobra/target/scala-2.13/gobra.jar"
additionalGobraArgs="--module github.com/ModularVerification/ReusableVerificationLibrary --include .verification --gobraDirectory $scriptDir/.gobra --parallelizeBranches"

packageName=$1
# If a packageName is provided as first argument, only this package is verified:
if [ -n "$packageName" ]; then
    echo "Verifying package $packageName"
    additionalGobraArgs="$additionalGobraArgs --includePackages $packageName"
fi

if [ $isCi ]; then
    echo -e "\033[0Ksection_start:`date +%s`:verify[collapsed=true]\r\033[0KVerifying packages"
fi
$preArgs -Xss128m -jar $gobraJar --recursive -I $scriptDir $additionalGobraArgs
>>>>>>> 715ef063c5c224d156bb0f96c681d547154b1149
exitCode=$?
if [ $isCi ]; then
    echo -e "\033[0Ksection_end:`date +%s`:verify\r\033[0K"
fi

# set exit code:
exit $exitCode
