#!/bin/sh
# Script to run this tool locally.
# Not suitable for short-lived VMs such as those provided for CI/CD.
#
# On Debian and Ubuntu, install dependencies with:
# sudo apt-get install libecm-dev gmp-ecm cargo
mkfifo composites || true
./build.sh
cargo +nightly run --release 2>&1 | tee /tmp/rust.log &
./yafu.sh <composites 2>&1 | tee /tmp/yafu.log &
