#!/bin/sh
# Script to run this tool locally.
# Not suitable for short-lived VMs such as those provided for CI/CD.
#
# On Debian and Ubuntu, install dependencies with:
# sudo apt-get install libecm-dev gmp-ecm cargo
./build.sh
RUST_BACKTRACE=full nice -+19 ./target/release/ScrapeFactordbPrpsRust 2>&1 | tee /tmp/rust.log | sed -E 's/(.{1000}).*$/\1.../'
