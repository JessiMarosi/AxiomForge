import MiniProver.Workbench.Skeleton

/-!
Phase 18 — Step 2 (Contract):
`MiniProver.Workbench.Skeleton` is part of the stable public API surface.

This test asserts:
- the module imports as a downstream consumer would
- `Skeleton.empty` is definitionally an empty skeleton (`rfl`)
-/

namespace MiniProver.Tests

open MiniProver.Workbench

theorem skeleton_empty_assumptions :
    (Skeleton.empty.assumptions = []) := by
  rfl

theorem skeleton_empty_obligations :
    (Skeleton.empty.obligations = []) := by
  rfl

end MiniProver.Tests
