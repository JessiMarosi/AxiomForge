import MiniProver.Workbench.Formulation
import MiniProver.Workbench.Assumptions
import MiniProver.Workbench.Skeleton
import MiniProver.Workbench.Failure
import MiniProver.Workbench.Analytic.P0

namespace MiniProver.Workbench

/--
Analytic normal form output (v0).

Intentionally minimal:
- a single rendered `tag` string that is deterministic and audit-friendly.
-/
structure AnalyticNormalForm where
  tag : String
deriving Repr, DecidableEq

namespace Analytic

/--
Analytic normalization layer (v0).

This layer normalizes a formulation using explicitly provided structured P0 inputs.

Rules:
- No Prop / Expr inspection
- No heuristics
- No inference
- No assumption smuggling

Note:
- v0 is *shape-only*: it produces a deterministic textual normal form tag.
- This is kept computable so the Dashboard CLI can remain executable.
-/
def toNormalForm (f : Formulation) : Except Failure AnalyticNormalForm :=
  match Analytic.p0For f with
  | none =>
      Except.error {
        kind := FailureKind.internalInvariant
        message :=
          "RH-A v0: no structured P0 shape registered for this formulation ID (add it to Analytic.p0For)"
        context := some "MiniProver.Workbench.Analytic.toNormalForm"
      }
  | some p0 =>
      let tag :=
        "NF_BigO(Real): ∃C>0 ∃x0>0 ∀x≥x0, |" ++ p0.fName ++ " - " ++ p0.gName ++
        "| ≤ C*(" ++ p0.hName ++ ")"
      Except.ok (AnalyticNormalForm.mk tag)

end Analytic
end MiniProver.Workbench
