#!/bin/bash

# this script is invoked as part of CI to verify all packages

# gather all top-level directories which we will consider as 
# packages that should be verified:

scriptDir=$(dirname "$0")

# flag whether this script is currently executed as part of a CI
isCi=$CI

gobraJar="/gobra/gobra.jar"
additionalGobraArgs="--module gitlab.inf.ethz.ch/arquintl/prototrace"

# `-exec basename {} \;` makes sure that the leading "./" is dropped from every package name
packages=$(find $scriptDir -type d -mindepth 1 -maxdepth 1 -exec basename {} \; | sort)

# catch ctrl+c such that not only verification of current package is aborted but all verifications:
trap "exit" SIGHUP SIGINT SIGTERM

TXT_RED="\033[31m"
TXT_GREEN="\033[32m"
TXT_BLUE="\033[34m"
TXT_CLEAR="\033[0m"
overallExitCode=0
for package in $packages; do
    # skip folders starting with '.':
    if [[ $package == .* ]]; then
        continue
    fi
    if [ $isCi ]; then
        echo -e "\033[0Ksection_start:`date +%s`:verify_$package[collapsed=true]\r\033[0KVerifying package ${TXT_BLUE}$package${TXT_CLEAR}"
    else
        echo -e "Verifying package ${TXT_BLUE}$package${TXT_CLEAR}"
    fi
    java -Xss128m -jar $gobraJar -i "$scriptDir/$package" -I "$scriptDir/$package" -I $scriptDir $additionalGobraArgs
    exitCode=$?
    if [ $isCi ]; then
        echo -e "\033[0Ksection_end:`date +%s`:verify_$package\r\033[0K"
    fi
    if [ $exitCode -eq 0 ]; then
        if [ ! $isCi ]; then
            echo -e "Verification of package ${TXT_GREEN}$package${TXT_CLEAR} succeeded"
        fi
    else
        echo -e "Verification of package ${TXT_RED}$package${TXT_CLEAR} failed (with exit code $exitCode)"
    fi
    # set overall exit code to first non-zero exitCode:
    if [ $overallExitCode -eq 0 ]; then
        overallExitCode=$exitCode
    fi
done

# set exit code:
exit $overallExitCode

