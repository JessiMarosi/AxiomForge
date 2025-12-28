/-
Phase 24 — Analytic normal forms (Step 1)

Scaffold only:
- establishes a stable public namespace for analytic normal-form work
- defines typed placeholders for later phases

No analysis, no heavy imports, no automation.
-/

import MiniProver.Workbench.Formulation
import MiniProver.Workbench.Assumptions
import MiniProver.Workbench.Skeleton
import MiniProver.Workbench.Failure

namespace MiniProver.Workbench

/--
A placeholder “analytic normal form” artifact.

This is intentionally opaque in Phase 24 Step 1.
Later phases may refine this into a structured object.
-/
structure AnalyticNormalForm where
  tag : String
  deriving Repr, DecidableEq

namespace Analytic

/--
A total, deterministic placeholder transformation.

Current behavior: always fails with `internalInvariant` because analytic content
is not implemented yet. This prevents accidental overclaiming.

Later phases may implement a real transformation and return `Except.ok`.
-/
def toNormalForm (_f : Formulation) : Except Failure AnalyticNormalForm :=
  Except.error { kind := FailureKind.internalInvariant
                 message := "Analytic normal form not implemented (Phase 24 scaffold only)."
                 context := some "MiniProver.Workbench.Analytic.toNormalForm" }

end Analytic
end MiniProver.Workbench
