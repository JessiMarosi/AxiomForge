#!/usr/bin/env bash
set -euo pipefail

cd /home/jsmar/axiom-forge

# 1) Deterministic full build
lake build

# 2) Import policy enforcement (layering + no ghost imports)
./scripts/import_policy_check.sh

echo "policy_check: OK"
