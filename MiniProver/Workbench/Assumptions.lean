/-
Phase 21 — Assumption ledger scaffold (Step 3)

Defines a minimal, deterministic assumption ledger:
- named assumptions (String)
- each with an explicit Prop

No inference, no checking, no automation.
-/

namespace MiniProver.Workbench

/-- A named assumption entry. -/
structure Assumption where
  name : String
  stmt : Prop

/-- A deterministic ledger: an ordered list of named assumptions. -/
abbrev AssumptionLedger := List Assumption

namespace Assumptions

/-- Empty ledger. -/
def empty : AssumptionLedger := []

end Assumptions
end MiniProver.Workbench
