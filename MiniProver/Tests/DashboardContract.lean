import MiniProver.Workbench.Dashboard

/-!
Phase 25 — Step 1 (Contract):
Dashboard renderers exist and are pure/deterministic.
-/

namespace MiniProver.Tests

open MiniProver.Workbench

def dummyFormulation : Formulation :=
  { id := "dummy", stmt := True }

def dummyStep : ReductionStep :=
  { name := "identity"
    src := dummyFormulation
    dst := dummyFormulation
    assumptions := Assumptions.empty
    skeleton := Skeleton.empty }

-- Contracts: renderers are total and produce Strings.
theorem dashboard_renders_reduction : (Dashboard.renderReduction dummyStep).length ≥ 0 := by
  simp

theorem dashboard_renders_analytic : (Dashboard.renderAnalytic dummyFormulation).length ≥ 0 := by
  simp

end MiniProver.Tests
