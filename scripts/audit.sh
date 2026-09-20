#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_source.py
lake env python3 scripts/check_module_resolution.py
lake build
for source in audit/*.lean; do
  lake env lean "$source"
done
git diff --check
