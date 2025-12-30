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
    -- PNT / Chebyshev ψ(x) error term shape (demo baseline)
    some { fName := "0", gName := "0", hName := "sqrt(x) * (log x)^2" }
  else if form.id == "mertens_equivalence" then
    -- Mertens route (P0 only): target *shape* for the summatory Möbius bound.
    -- We are NOT proving it, only declaring the intended Big-O family.
    -- Conventional statement (informal): M(x) = O(x^(1/2+ε)) for all ε>0
    -- We keep ε symbolic at v0: "x^(1/2+ε)".
    some { fName := "M(x)", gName := "0", hName := "x^(1/2+ε)" }
  else if form.id == "nyman_beurling" then
    -- Nyman–Beurling route (P0 only): placeholder Big-O shape for analytic burden.
    -- Goal here is classification (move bottleneck to BridgeSpec), not proof.
    some { fName := "NB(x)", gName := "0", hName := "x^(1/2+ε)" }
  else
    none

end Analytic
end MiniProver.Workbench
