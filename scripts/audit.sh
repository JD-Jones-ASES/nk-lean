#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
for source in audit/*.lean; do
  lake env lean "$source"
done
git diff --check
