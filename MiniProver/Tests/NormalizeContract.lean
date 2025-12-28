import MiniProver.Workbench.Normalize

/-!
Phase 15 — Step 3 (Contract):
`MiniProver.Workbench.Normalize` is part of the stable public API surface.

This test asserts:
- the module imports as a downstream consumer would
- `normalize` is definitional identity (rfl)
-/

namespace MiniProver.Tests

open MiniProver.Workbench

theorem normalize_is_identity (x : Nat) :
    Normalize.normalize x = x := by
  rfl

end MiniProver.Tests
