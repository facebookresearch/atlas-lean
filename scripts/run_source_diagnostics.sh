#!/usr/bin/env bash
# Source diagnostics: the focused tests, then both scanners over every
# extension library. Findings are advisory (--report-only), but failed tests,
# missing inputs and scan errors fail. Run it from the repository root; the
# Source diagnostics workflow runs it on every PR and merge group.
set -euo pipefail
python3 -m unittest discover -s scripts -p test_week2_ci.py -v
python3 scripts/check_duplicate_defs.py --report-only --require-declarations \
  CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest Domains DomainsTest WantedExt
python3 scripts/check_hypothesis_debt.py --report-only --require-declarations \
  CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest Domains DomainsTest WantedExt
