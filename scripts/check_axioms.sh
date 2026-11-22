#!/usr/bin/env bash
# Inspect every compiled project module in isolated, initialized environments.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"
python3 scripts/audit_compiled_modules.py
