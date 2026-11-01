#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification
check_log=$(mktemp verification/.check.XXXXXX)
run_checks() {
  python3 scripts/check_layout.py || return
  lake build || return
  lake env lean -DautoImplicit=false Audit.lean
}
if run_checks 2>&1 | tee "$check_log"; then
  if python3 scripts/check_layout.py --record "$check_log"; then
    mv "$check_log" verification/check.log
  else
    mv "$check_log" verification/failed.log
    exit 1
  fi
else
  mv "$check_log" verification/failed.log
  exit 1
fi
