import MiniProver.Workbench.Analytic.P0

namespace MiniProver.Workbench.Analytic

/-- P0+ layer: declarative bridge obligations (no proofs). -/
structure Obligation where
  key  : String
  desc : String
deriving Repr, DecidableEq

structure BridgeSpec where
  formulationId : String
  obligations   : List Obligation
deriving Repr, DecidableEq

def bridgeFor : String → Option BridgeSpec
  | "mertens_equivalence" =>
      some {
        formulationId := "mertens_equivalence"
        obligations := [
          { key := "def_M", desc := "Declare M(x) (Mertens function) with cutoff conventions." },
          { key := "bridge_mu", desc := "Link M(x) to μ(n) partial sums." },
          { key := "route_to_zeta", desc := "Declare route to ζ(s) (Dirichlet / Perron / explicit formula), shape-only." },
          { key := "error_terms", desc := "List all error-term obligations introduced by the route." }
        ]
      }
  | _ => none

end MiniProver.Workbench.Analytic
