import MiniProver.Workbench.Analytic.P1

namespace MiniProver.Workbench.Analytic

/--
Phase 15.4 — Stub registry (proof-free).

A stub is just a named marker that an obligation has a concrete placeholder
in the codebase. It does not assert truth; it asserts "this obligation has
a tracked place to be discharged later."
-/
def HasStub (name : String) : Bool :=
  name == "mertens_equivalence.def_M"

end MiniProver.Workbench.Analytic
