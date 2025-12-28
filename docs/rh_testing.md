# RH Testing Framework

Axiom Forge includes a deterministic, auditable workflow for **testing published RH-equivalent statements** and RH-related reductions.

**Purpose (LOCKED):**  
The purpose of this framework is not to advance analytic number theory, but to demonstrate that RH-equivalent formulations can be reduced to a finite, auditable set of typed analytic obligations under strict determinism.

## What this is (and is not)

- **Is:** a formal reduction / elimination instrument (proof checking + obligation surfacing + explicit failure points)
- **Is not:** a solver, oracle, conjecture generator, or heuristic engine

## Registry structure

The RH registry lives in:

- `rh_testing/`

Key subfolders:

- `tested/` — tested entries with authoritative `status.txt` + `dashboard_artifact.txt`
- `compilation/` — global roll-ups:
  - `SUMMARY.txt` (machine-stable)
  - `SUMMARY.md` (human-readable mirror)
  - `index.json` (structured registry)
  - `history/` (immutable daily snapshots)

Status semantics are defined in:

- `rh_testing/README.md`

## Evidence requirement

Every tested entry must include a **verbatim dashboard artifact** as evidence.  
Failures must record a concrete failure point (module/function/lemma), not a narrative explanation.

## Current limitations (honest boundary)

The analytic layer includes an explicit scaffold boundary (e.g. analytic normal form may be intentionally unimplemented).  
In such cases the framework must fail explicitly and deterministically rather than bluffing.

