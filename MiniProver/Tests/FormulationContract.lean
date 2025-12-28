import MiniProver.Workbench.Formulation

/-!
Phase 21 — Step 2 (Contract):
`MiniProver.Workbench.Formulation` is part of the stable public API surface.

This test asserts:
- the module imports as a downstream consumer would
- `Formulation.ofStmt` is definitionally the expected record (`rfl`)
-/

namespace MiniProver.Tests

open MiniProver.Workbench

theorem formulation_ofStmt_defeq (id : FormulationId) (P : Prop) :
    Formulation.ofStmt id P = { id := id, stmt := P } := by
  rfl

end MiniProver.Tests
