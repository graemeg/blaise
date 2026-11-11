#!/bin/bash
# windows-e2e-runner.sh <exe> [args] -- the e2e harness's runner for the
# Windows guest: BLAISE_E2E_TARGET=windows-x86_64
# BLAISE_E2E_RUNNER=<repo>/scripts/windows-e2e-runner.sh compiler/target/TestRunner
# compiles each e2e program for Windows and runs it in the guest.
exec "$(dirname "$0")/windows-vm.sh" e2e-run "$@"
