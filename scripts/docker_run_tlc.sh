#!/usr/bin/env bash
set -euo pipefail

MODE="${1:-smoke}"
LOG_ROOT="${LOG_DIR:-/workspace/verification_logs}"
LOG_DIR="$LOG_ROOT/tlc_results"
mkdir -p "$LOG_DIR"

echo "========================================="
echo "Solana Alpenglow TLC Verification"
echo "Running inside Docker (mode=$MODE)"
echo "========================================="
echo ""

JAVA_INFO=$(java -version 2>&1 | head -n1 || true)
echo "Java: $JAVA_INFO"
echo "Tools: /workspace/tools/tla2tools.jar"
echo "Logs:  $LOG_DIR"
echo ""

run_tlc() {
  local cfg="$1"
  local cfg_file="/workspace/configs/${cfg}.cfg"
  local log_file="${LOG_DIR}/${cfg}_$(date +%Y%m%d_%H%M%S).log"
  if [ ! -f "$cfg_file" ]; then
    echo "Config not found: $cfg_file" >&2
    return 1
  fi
  echo "=== TLC: ${cfg} ==="
  java -XX:+UseParallelGC -Xmx8G -Xms2G \
    -cp /workspace/tools/tla2tools.jar tlc2.TLC \
    -workers auto -coverage 1 -deadlock -cleanup \
    -config "$cfg_file" \
    /workspace/tla/AlpenglowMC.tla 2>&1 | tee "$log_file"
  echo ""
}

case "$MODE" in
  smoke)
    CFGS=("AlpenglowMC_4val_fast")
    ;;
  quick)
    CFGS=("AlpenglowMC_4val_fast" "AlpenglowMC_6val_fast")
    ;;
  full)
    CFGS=("AlpenglowMC_4val" "AlpenglowMC_6val" "AlpenglowMC_8val" "AlpenglowMC_10val")
    ;;
  *)
    echo "Unknown mode: $MODE" >&2
    exit 2
    ;;
esac

for c in "${CFGS[@]}"; do
  run_tlc "$c" || true
done

echo "========================================="
echo "TLC verification finished (mode=$MODE)"
echo "Logs in: $LOG_DIR"
echo "========================================="
