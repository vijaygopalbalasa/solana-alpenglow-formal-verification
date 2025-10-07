#!/usr/bin/env bash
set -euo pipefail

missing=()

check_cmd() {
  local name="$1"
  local hint="$2"
  if ! command -v "$name" >/dev/null 2>&1; then
    if [[ "$name" = "java" && -n "$JAVA_HOME" && -x "$JAVA_HOME/bin/java" ]]; then
      echo "[OK] java -> $JAVA_HOME/bin/java"
      "$JAVA_HOME/bin/java" -version 2>&1 | head -n 1
      return
    fi
    echo "[MISSING] $name – $hint"
    missing+=("$name")
  else
    echo "[OK] $name -> $(command -v "$name")"
    if "$name" --version >/dev/null 2>&1; then
      "$name" --version 2>&1 | head -n 1
    else
      echo "[WARN] $name exists but '--version' failed"
      missing+=("$name")
    fi
  fi
}

echo "== Checking Java =="
check_cmd java "Install OpenJDK 11+ (e.g. brew install openjdk@21)"

echo "\n== Checking TLAPS =="
if [[ -x "tools/tlapm/bin/tlapm" ]]; then
  echo "[OK] TLAPS binary present at tools/tlapm/bin/tlapm"
  if tools/tlapm/bin/tlapm --version >/dev/null 2>&1; then
    tools/tlapm/bin/tlapm --version
  else
    echo "[WARN] Unable to execute TLAPS (sandbox may forbid /bin/ps)."
  fi
else
  echo "[MISSING] TLAPS binary – rebuild from https://github.com/tlaplus/tlapm"
  missing+=("tlapm")
fi

echo "\n== Checking Rust =="
check_cmd cargo "Install via https://rustup.rs"

if (( ${#missing[@]} )); then
  echo "\nPrerequisite check failed: missing ${missing[*]}" >&2
  exit 1
fi

echo "\nAll prerequisites detected."
