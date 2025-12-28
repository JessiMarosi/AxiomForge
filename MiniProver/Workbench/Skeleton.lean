/-
Phase 18 — Proof skeleton emission (Step 1)

This module defines a minimal, deterministic representation of a proof skeleton.
A proof skeleton is NOT a proof and performs NO automation.

It exists to:
- enumerate required obligations
- record assumptions explicitly
- provide a typed, auditable structure for later completion
-/

import MiniProver.Workbench.Assumptions

namespace MiniProver.Workbench

/-- A named proof obligation with a proposition to be proved. -/
structure Obligation where
  name : String
  goal : Prop

/--
A proof skeleton consists of:
- explicit assumptions (as a named ledger)
- a finite list of named obligations
-/
structure ProofSkeleton where
  assumptions : AssumptionLedger
  obligations : List Obligation

namespace Skeleton

/--
A trivial constructor for an empty skeleton.
Used to validate the API surface.
-/
def empty : ProofSkeleton :=
  { assumptions := Assumptions.empty, obligations := [] }

end Skeleton
end MiniProver.Workbench
