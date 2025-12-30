import MiniProver.Workbench.Formulation
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace MiniProver.Workbench
namespace Analytic

/--
P0 input (v0): the minimal structured “target bound shape” we allow a formulation to provide
to the analytic normal-form layer.

We keep it deliberately small and deterministic:
- only Real → Real functions
- only the Big-O “|f - g| ≤ C * h” shape
- no Prop/Expr introspection
- no heuristics
- no parsing
- no automation

Later phases may widen this, but v0 exists to eliminate ad-hoc special-casing.
-/
structure P0BigO where
  f : Real → Real
  g : Real → Real
  h : Real → Real

/--
Registry (v0): map *known* formulation IDs to a structured P0 shape.

This is intentionally explicit and boring:
- deterministic
- auditable
- no inference

If an ID is missing here, that is a clear, actionable failure: "no P0 shape provided".
-/
def p0For (form : Formulation) : Option P0BigO :=
  if form.id == "pnt_error_chebyshev_psi" then
    -- Same h used in your current success path.
    let h : Real → Real := fun x => Real.sqrt x * (Real.log x) ^ (2 : Nat)
    some { f := fun _ => 0, g := fun _ => 0, h := h }
  else
    none

end Analytic
end MiniProver.Workbench
