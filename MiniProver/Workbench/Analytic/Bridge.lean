import MiniProver.Workbench.Analytic.P0
import MiniProver.Workbench.Analytic.P1
import MiniProver.Workbench.Analytic.Stubs
import MiniProver.Workbench.Analytic.Assumptions

namespace MiniProver.Workbench.Analytic

structure BridgeSpec where
  formulationId : String
  obligations   : List P1Obligation
  /-
  Assumption ledger (v1): audit-grade bookkeeping only.
  Default is empty to preserve existing behavior.
  -/
  assumptions   : AssumptionLedger := AssumptionLedger.empty
deriving Repr, DecidableEq

/-- Helper: qualify an obligation name to avoid collisions across formulations. -/
def q (formId key : String) : String :=
  formId ++ "." ++ key

def bridgeFor : String → Option BridgeSpec
  | "mertens_equivalence" =>
      let fid := "mertens_equivalence"
      some {
        formulationId := fid
        obligations := [
          { name := q fid "def_M",
            description := "Declare M(x) (Mertens function) with cutoff conventions.",
            hasStub := HasStub (q fid "def_M") },
          { name := q fid "bridge_mu",
            description := "Link M(x) to μ(n) partial sums.",
            hasStub := HasStub (q fid "bridge_mu") },
          { name := q fid "route_to_zeta",
            description := "Declare route to ζ(s) (Dirichlet / Perron / explicit formula), shape-only.",
            hasStub := HasStub (q fid "route_to_zeta") },
          { name := q fid "error_terms",
            description := "List all error-term obligations introduced by the route.",
            hasStub := HasStub (q fid "error_terms") }
        ]
        -- assumptions defaults to empty
      }

  | "pnt_error_chebyshev_psi" =>
      let fid := "pnt_error_chebyshev_psi"
      some {
        formulationId := fid
        obligations := [
          { name := q fid "def_psi",
            description := "Declare Chebyshev ψ(x) and Λ(n) with cutoff conventions.",
            hasStub := HasStub (q fid "def_psi") },
          { name := q fid "route_explicit_formula",
            description := "Declare explicit-formula-style route tying ψ(x)-x to ζ zeros, shape-only.",
            hasStub := HasStub (q fid "route_explicit_formula") },
          { name := q fid "smoothing_truncation",
            description := "List smoothing/truncation obligations and named error terms introduced.",
            hasStub := HasStub (q fid "smoothing_truncation") },
          { name := q fid "bound_goal",
            description := "Declare the target error bound family: O( sqrt(x) * (log x)^2 ).",
            hasStub := HasStub (q fid "bound_goal") }
        ]
        -- assumptions defaults to empty
      }

  | "nyman_beurling" =>
      let fid := "nyman_beurling"
      some {
        formulationId := fid
        obligations := [
          { name := q fid "def_nb_space",
            description := "Declare the Nyman–Beurling function space / closure statement being used, shape-only.",
            hasStub := HasStub (q fid "def_nb_space") },
          { name := q fid "bridge_to_zeta",
            description := "Declare the bridge from the closure criterion to ζ(s) nonvanishing / RH, shape-only.",
            hasStub := HasStub (q fid "bridge_to_zeta") },
          { name := q fid "approx_family",
            description := "Name the approximation family (e.g., fractional part functions) and required closure obligations.",
            hasStub := HasStub (q fid "approx_family") },
          { name := q fid "norm_topology",
            description := "Declare the norm/topology and any measure-theory obligations introduced by the criterion.",
            hasStub := HasStub (q fid "norm_topology") }
        ]
        -- assumptions defaults to empty
      }

  | "robin_inequality" =>
      some {
        formulationId := "robin_inequality"
        obligations := [
          { name := q "robin_inequality" "def_sigma",
            description := "Declare σ(n) (sum of divisors) with domain conventions and notation.",
            hasStub := HasStub (q "robin_inequality" "def_sigma") },
          { name := q "robin_inequality" "def_gamma_const",
            description := "Declare Euler–Mascheroni γ and constants used in e^γ n log log n, shape-only.",
            hasStub := HasStub (q "robin_inequality" "def_gamma_const") },
          { name := q "robin_inequality" "bridge_to_zeta",
            description := "Declare the equivalence bridge: Robin’s inequality ↔ RH, naming the route and required ζ(s) facts, shape-only.",
            hasStub := HasStub (q "robin_inequality" "bridge_to_zeta") },
          { name := q "robin_inequality" "threshold_5041",
            description := "Declare the threshold obligation n ≥ 5041 and handling of finite exceptions, shape-only.",
            hasStub := HasStub (q "robin_inequality" "threshold_5041") }
        ]
        assumptions :=
          AssumptionLedger.add AssumptionLedger.empty AssumptionTag.bridgeAxiom
            "Robin ↔ RH bridge is declarative placeholder; not a proof."
      }

  | _ => none

end MiniProver.Workbench.Analytic
