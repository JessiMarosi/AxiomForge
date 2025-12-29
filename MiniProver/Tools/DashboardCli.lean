/-
Phase 22 — Dashboard CLI (deterministic)

Provides a small CLI wrapper around the Axiom Forge dashboard views.
No automation, no dynamic loading, no file IO.
-/

import MiniProver.Workbench.Formulation
import MiniProver.Workbench.Reduction
import MiniProver.Workbench.Dashboard

open MiniProver.Workbench

/-- Usage string printed by the CLI. -/
def usage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  axiom_dashboard            # same as: all"
    , "  axiom_dashboard all"
    , "  axiom_dashboard reduction"
    , "  axiom_dashboard analytic"
    , "  axiom_dashboard help"
    ]

/-
Demo artifacts (used by reduction view).
These are intentionally simple and deterministic.
-/
def demoFormulation : Formulation :=
  Formulation.ofStmt "demo" True

def demoStep : ReductionStep :=
  { name := "demo"
  , src := demoFormulation
  , dst := demoFormulation
  , assumptions := Assumptions.empty
  , skeleton := Skeleton.empty
  }

/-
RH demo formulations used by the analytic view.
We only inspect `id` at RH-A.5A; `stmt` is opaque for now.
-/
def rhDemoFormulations : List Formulation :=
  [ Formulation.ofStmt "mertens_equivalence" True
  , Formulation.ofStmt "nyman_beurling" True
  , Formulation.ofStmt "pnt_error_chebyshev_psi" True
  ]

/-- Run a selected dashboard view. -/
def runView (view : String) : IO UInt32 := do
  match view with
  | "all" =>
      IO.println (Dashboard.renderReduction demoStep)
      IO.println ""
      for f in rhDemoFormulations do
        IO.println s!"== {f.id} =="
        IO.println (Dashboard.renderAnalytic f)
        IO.println ""
      pure 0

  | "reduction" =>
      IO.println (Dashboard.renderReduction demoStep)
      pure 0

  | "analytic" =>
      for f in rhDemoFormulations do
        IO.println s!"== {f.id} =="
        IO.println (Dashboard.renderAnalytic f)
        IO.println ""
      pure 0

  | "help" =>
      IO.println usage
      pure 0

  | _ =>
      IO.println s!"Unknown view: {view}\n"
      IO.println usage
      pure 2

/-
IMPORTANT:
Lake passes CLI arguments directly to `main`.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | []        => runView "all"
  | view :: _ => runView view
