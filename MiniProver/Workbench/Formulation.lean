/-
Phase 21 — Typed formulation registry (Step 1)

This module defines a minimal, deterministic representation of a "formulation":
a named, typed problem statement (a Prop) with structured metadata.

No automation, no search, no proof generation.
-/

namespace MiniProver.Workbench

/-- A stable identifier for a registered formulation. -/
abbrev FormulationId := String

/-- A minimal formulation record: ID + statement. -/
structure Formulation where
  id : FormulationId
  stmt : Prop

namespace Formulation

/-- Deterministic helper (avoids name clash with the structure constructor). -/
def ofStmt (id : FormulationId) (stmt : Prop) : Formulation :=
  { id := id, stmt := stmt }

end Formulation
end MiniProver.Workbench
