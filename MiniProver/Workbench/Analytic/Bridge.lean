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

  | "pnt_error_chebyshev_psi" =>
      some {
        formulationId := "pnt_error_chebyshev_psi"
        obligations := [
          { key := "def_psi", desc := "Declare Chebyshev ψ(x) and Λ(n) with cutoff conventions." },
          { key := "route_explicit_formula", desc := "Declare explicit-formula-style route tying ψ(x)-x to ζ zeros, shape-only." },
          { key := "smoothing_truncation", desc := "List smoothing/truncation obligations and named error terms introduced." },
          { key := "bound_goal", desc := "Declare the target error bound family: O( sqrt(x) * (log x)^2 )." }
        ]
      }

  | "nyman_beurling" =>
      some {
        formulationId := "nyman_beurling"
        obligations := [
          { key := "def_nb_space", desc := "Declare the Nyman–Beurling function space / closure statement being used, shape-only." },
          { key := "bridge_to_zeta", desc := "Declare the bridge from the closure criterion to ζ(s) nonvanishing / RH, shape-only." },
          { key := "approx_family", desc := "Name the approximation family (e.g., fractional part functions) and required closure obligations." },
          { key := "norm_topology", desc := "Declare the norm/topology and any measure-theory obligations introduced by the criterion." }
        ]
      }

  | _ => none

end MiniProver.Workbench.Analytic
