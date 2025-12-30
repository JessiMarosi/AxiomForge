import MiniProver.Workbench.Formulation

namespace MiniProver.Workbench
namespace Analytic

/--
P0 input (v0, computable): minimal structured “target bound shape” for analytic normalization.

We store *names* of f, g, h instead of actual functions to keep the dashboard CLI executable.
No evaluation occurs at this phase; the goal is deterministic normalization of the bound *shape*.
-/
structure P0BigO where
  fName : String
  gName : String
  hName : String

/--
Registry (v0): explicit mapping from formulation IDs to structured P0 shapes.

If an ID is missing here, the analytic layer should fail with a clear error.
-/
def p0For (form : Formulation) : Option P0BigO :=
  if form.id == "pnt_error_chebyshev_psi" then
    some { fName := "0", gName := "0", hName := "sqrt(x) * (log x)^2" }
  else
    none

end Analytic
end MiniProver.Workbench
