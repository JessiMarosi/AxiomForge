namespace MiniProver.Workbench.Analytic

/--
Phase 15 (P1) — Typed obligation tokens.

These are *declarative* placeholders for analytic/bridge obligations.
At P1, nothing is proven. We only make obligations:
- name-stable
- countable
- audit-visible
- linkable to future stubs/proofs
-/
structure P1Obligation where
  /-- Stable identifier used for dashboards and comparisons. -/
  name : String
  /-- Human-readable explanation of what must eventually be discharged. -/
  description : String
  /-- Whether a lemma stub exists (proof may still be absent). -/
  hasStub : Bool := false
deriving Repr, DecidableEq

end MiniProver.Workbench.Analytic
