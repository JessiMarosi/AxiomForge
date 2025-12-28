#!/usr/bin/env bash
set -euo pipefail

echo "[Axiom Forge] clean_build: starting"
echo "[Axiom Forge] repo: $(pwd)"

# Remove Lean/Lake build outputs for this repo only (no personal files).
rm -rf .lake/build

echo "[Axiom Forge] removed .lake/build"
echo "[Axiom Forge] running: lake build"
lake build

echo "[Axiom Forge] clean_build: success"
