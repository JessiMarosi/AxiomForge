import MiniProver.Workbench.Formulation
import MiniProver.Workbench.Assumptions
import MiniProver.Workbench.Skeleton
import MiniProver.Workbench.Failure
import MiniProver.Workbench.Analytic.NormalForm
import MiniProver.Workbench.Analytic.P0

noncomputable section

namespace MiniProver.Workbench

/--
Analytic normal form output (v0).

This is intentionally minimal:
- a single rendered `tag` string that is deterministic and audit-friendly

Later phases may extend this structure, but v0 is a stable output surface for the dashboard.
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

Failure is expected unless a formulation explicitly registers a P0 shape.
-/
def toNormalForm (f : Formulation) : Except Failure AnalyticNormalForm :=
  match Analytic.p0For f with
  | none =>
      Except.error {
        kind := FailureKind.internalInvariant
        message :=
          "RH-A v0: no structured P0 shape registered for this formulation ID " ++
          "(add it to Analytic.p0For)"
        context := some "MiniProver.Workbench.Analytic.toNormalForm"
      }
  | some p0 =>
      let nf : NormalForm := NormalForm.bigO p0.f p0.g p0.h
      Except.ok (AnalyticNormalForm.mk nf.render)

end Analytic
end MiniProver.Workbench
