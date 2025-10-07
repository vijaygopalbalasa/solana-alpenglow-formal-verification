#!/bin/sh
# Wrapper for TLAPM that provides ps stub
export PATH="$HOME/bin:$PATH"
export TLA_PATH="$(pwd)/tla:$(pwd)/proofs"
exec tools/tlapm/bin/tlapm "$@"
