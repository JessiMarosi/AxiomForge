/-
Phase 14 — Workbench API Contract Tests
Step 2 (Negative): downstream consumers must not import `MiniProver.Library.*`.

NOTE:
This contract cannot be validated from inside the same Lean package with `fail_if_success`
because module imports happen at the *build level*, not as a tactic-level action.

The enforcement check for this step is performed by building the intentionally-forbidden
consumer module and requiring that build to FAIL:

  ! lake build MiniProver.Tests._ForbiddenConsumerImportsLibrary

If that command succeeds, the boundary is broken.
-/
namespace MiniProver.Tests
theorem workbench_contract_negative_compiles : True := by
  trivial
end MiniProver.Tests
