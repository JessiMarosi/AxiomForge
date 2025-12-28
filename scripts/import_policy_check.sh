#!/usr/bin/env bash
set -euo pipefail

cd /home/jsmar/axiom-forge

# Rule 1: Tests must not import internal Library
lake exe import_gate -- MiniProver/Tests "import MiniProver.Library"

# Rule 2: Workbench must never depend on Tests
lake exe import_gate -- MiniProver/Workbench "import MiniProver.Tests"

# Rule 3: Library must never depend on Tests
lake exe import_gate -- MiniProver/Library "import MiniProver.Tests"

echo "import_policy_check: OK"
