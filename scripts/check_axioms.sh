#!/usr/bin/env bash
# Inspect every compiled project module in isolated, initialized environments.
# On a pull request, CI may scope this to the modules its build rewrote.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"
if [[ -n "${ATLAS_AUDIT_RESTORED:-}" ]]; then
  exec python3 scripts/audit_rebuilt_modules.py
fi
python3 scripts/audit_compiled_modules.py
