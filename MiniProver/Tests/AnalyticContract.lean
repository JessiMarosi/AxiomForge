import MiniProver.Workbench.Analytic

/-!
Phase 24 — Step 2 (Contract):
Analytic normal-form work is scaffold-only and must not overclaim.

This test asserts:
- module imports as a downstream consumer would
- `Analytic.toNormalForm` deterministically returns `Except.error`
- error kind is `FailureKind.internalInvariant`
-/

namespace MiniProver.Tests

open MiniProver.Workbench

def dummyFormulation : Formulation :=
  { id := "dummy", stmt := True }

theorem analytic_toNormalForm_returns_error :
    match Analytic.toNormalForm dummyFormulation with
    | Except.error _ => True
    | Except.ok _    => False := by
  simp [Analytic.toNormalForm]

theorem analytic_toNormalForm_error_kind :
    match Analytic.toNormalForm dummyFormulation with
    | Except.error f => f.kind = FailureKind.internalInvariant
    | Except.ok _    => False := by
  simp [Analytic.toNormalForm]

end MiniProver.Tests
