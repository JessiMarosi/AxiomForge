import MiniProver.Workbench.Analytic.RobinBridge
import MiniProver.Workbench.Formulation
import MiniProver.Workbench.Assumptions
import MiniProver.Workbench.Skeleton
import MiniProver.Workbench.Failure
import MiniProver.Workbench.Analytic.P0
import MiniProver.Workbench.Analytic.Bridge
import MiniProver.Workbench.Analytic.Mertens
import MiniProver.Workbench.Analytic.Robin
import MiniProver.Workbench.Analytic.Scaffold


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
      -- P0+ gate: require a declared BridgeSpec (obligation checklist) once P0 exists.
      match MiniProver.Workbench.Analytic.bridgeFor f.id with
      | none =>
          Except.error {
            kind := FailureKind.internalInvariant
            message :=
              s!"RH-A v0: missing BridgeSpec (P0+ obligations) for formulation ID {f.id} (add it to Analytic.bridgeFor)"
            context := some "MiniProver.Workbench.Analytic.toNormalForm"
          }
      | some _spec =>
          let tag :=
            "NF_BigO(Real): ∃C>0 ∃x0>0 ∀x≥x0, |" ++ p0.fName ++ " - " ++ p0.gName ++
            "| ≤ C*(" ++ p0.hName ++ ")"
          Except.ok (AnalyticNormalForm.mk tag)

end Analytic
end MiniProver.Workbench

