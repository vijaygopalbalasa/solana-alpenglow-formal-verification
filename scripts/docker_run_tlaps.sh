#!/usr/bin/env bash
set -euo pipefail

LOG_DIR="${LOG_DIR:-/workspace/verification_logs}"
mkdir -p "$LOG_DIR"

echo "========================================="
echo "Solana Alpenglow TLAPS Verification"
echo "Running inside Docker"
echo "========================================="
echo ""

tlapm --version

run_proof() {
  local label="$1"
  local module="$2"
  echo "=== ${label} ==="
  tlapm -C --stretch 6 -I proofs -I tla "${module}" 2>&1 | tee "${LOG_DIR}/tlaps_${label,,}_docker.log"
  echo ""
}

run_proof "QuorumIntersection" proofs/QuorumIntersection.tla
run_proof "CertificateUniqueness" proofs/CertificateUniqueness.tla
run_proof "FinalizationSafety" proofs/FinalizationSafety.tla

echo "========================================="
echo "Verification complete! Logs in ${LOG_DIR}"
echo "========================================="
