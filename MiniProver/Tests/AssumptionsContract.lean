import MiniProver.Workbench.Assumptions
import MiniProver.Workbench.Skeleton

/-!
Phase 21 — Step 4 (Contract):
Assumption ledger is part of the stable public API surface.

This test asserts:
- `Assumptions.empty` is definitionally empty (`rfl`)
- `Skeleton.empty.assumptions` is definitionally `Assumptions.empty` (`rfl`)
-/

namespace MiniProver.Tests

open MiniProver.Workbench

theorem assumptions_empty_defeq : (Assumptions.empty : AssumptionLedger) = [] := by
  rfl

theorem skeleton_empty_uses_assumptions_empty :
    Skeleton.empty.assumptions = Assumptions.empty := by
  rfl

end MiniProver.Tests
