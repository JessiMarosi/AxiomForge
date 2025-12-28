# RH Testing Registry (Axiom Forge)

This folder is a deterministic, auditable registry for testing **published RH-equivalent statements** and RH-related reductions.

**Policy:** no speculation, no probability language, no overclaiming.
Axiom Forge is not a solver. It is an instrument that records reductions, assumptions, obligations, and explicit failure points.

---

## Folder meanings

### `tested/`
A claim/reduction has been encoded and executed through the Axiom Forge pipeline (user-mode + dashboard artifact captured).
A test may still be marked **FAILED** inside its record if the pipeline reached a deterministic failure point.

### `failed/`
(Optional mirror) Items may be copied here if you want a physical separation for “failed outcomes.”
However, the authoritative status is always the `Status:` field inside `tested/<test>/status.txt`.

### `passed/`
Reserved for cases where all obligations are discharged under declared axioms and the reduction is fully verified.
This is expected to remain empty for a long time.

### `compilation/`
Global roll-ups generated from the registry:
- `SUMMARY.txt` (machine-stable)
- `SUMMARY.md` (human-readable mirror)
- `index.json` (structured status registry)
- `history/` (immutable daily snapshots)

---

## Status semantics (LOCKED)

All test entries MUST use exactly one of these status values:

- **TESTED**: reduction encoded; obligations surfaced; dashboard artifact captured; no conclusion asserted.
- **FAILED**: deterministic failure occurred (e.g. analytic boundary, contradiction, missing lemma). Failure point MUST be recorded.
- **PASSED**: all obligations discharged under stated axioms; fully verified end-to-end.

No other statuses are allowed.

---

## Required files for each test entry

Each test entry must be a folder under `tested/`:

`projects/rh_testing/tested/<test_id>/`

Required files:

1. `status.txt` (authoritative record)
2. `dashboard_artifact.txt` (verbatim copy of the latest dashboard artifact used as evidence)

Optional but recommended:

- `skeleton_ref.txt` (path to user-mode Lean skeleton file)
- additional supporting notes (only if factual and auditable)

---

## `status.txt` required fields

Minimum required sections:

- `Claim:`
- `Status:` (TESTED / FAILED / PASSED)
- `Failure Type:` (if FAILED)
- `Failure Point:` (if FAILED; must be a concrete module/function/lemma location)
- `Reason:` (if FAILED; concise)
- `Date Tested:` (YYYY-MM-DD)
- `Notes:` (factual only)

---

## Prohibited content

Do NOT include:

- “almost proved”, “close”, “probably”, “likely”, “I think this works”
- claims of solving RH
- unverifiable reasoning, anecdotes, opinions

This registry is not for brainstorming. It is for **auditable test records**.

---

## Contribution workflow (minimal)

1. Create a new folder under `tested/<test_id>/`
2. Add `status.txt`
3. Run the dashboard and copy the resulting artifact to `dashboard_artifact.txt`
4. Update `compilation/` summaries (Step RH-C.3 pattern)

