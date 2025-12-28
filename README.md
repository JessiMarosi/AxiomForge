# Axiom Forge

Axiom Forge is a **deterministic, auditable Lean 4 + mathlib–based formal reasoning instrument**.
It is **not** an oracle, solver, conjecture generator, or AI mathematician.

Its role is to:
- enforce formal correctness
- expose hidden assumptions
- normalize equivalent formulations
- eliminate invalid approaches early
- generate auditable proof skeletons
- support rigorous reduction workflows for extreme / unsolved problems

## What this is / what this is not

**Axiom Forge is:**
- a policy-governed, deterministic proof/verification instrument built on Lean 4 + mathlib
- a toolchain that makes dependencies and assumptions explicit
- a framework for producing auditable artifacts (contracts, negative tests, skeleton obligations)

**Axiom Forge is not:**
- a theorem-proving “oracle”
- a proof-search engine, conjecture generator, or heuristic system
- a substitute for mathematical insight
- a system that uses network access, telemetry, cloud execution, or external data

## Operating rules (enforced)

These rules govern development and are reflected in the repository structure and tests:
- **one step at a time**
- every action specifies: **Where · Why · How · What to expect · If it fails**
- **no speculative additions**
- new ideas must strengthen the current claim or be deferred
- **determinism & auditability override speed**
- **no UI before capability**
- **no overclaiming of mathematical power**

## Privacy rule (strict)

Only files inside the repository are tracked. In particular:
- `projects/` is ignored by git
- no personal files
- no external data
- no network access required for operation
- no telemetry, no cloud execution

## Repository layout (high-level)


