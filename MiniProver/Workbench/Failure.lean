/-
Phase 23 — Failure & boundary surfacing (Step 1)

Defines a minimal, deterministic failure surface for Axiom Forge.
No exceptions, no automation, no search.

This is structured data intended for:
- audit logs
- explicit boundary reporting
- later obligation compilation diagnostics
-/

namespace MiniProver.Workbench

/-- A deterministic category for surfaced failures. -/
inductive FailureKind where
  | invalidInput
  | missingAssumption
  | missingObligation
  | policyViolation
  | internalInvariant
  deriving Repr, DecidableEq

/-- A surfaced failure: kind + message + optional context tag. -/
structure Failure where
  kind : FailureKind
  message : String
  context : Option String := none
  deriving Repr, DecidableEq

namespace Failure

/-- Deterministic helper: attach context. -/
def withContext (f : Failure) (ctx : String) : Failure :=
  { f with context := some ctx }

end Failure
end MiniProver.Workbench
