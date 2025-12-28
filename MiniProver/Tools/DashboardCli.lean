import MiniProver.Workbench.Dashboard

/-!
End-user dashboard CLI (views)

Usage:
  axiom_dashboard            # same as: all
  axiom_dashboard all
  axiom_dashboard reduction
  axiom_dashboard analytic
  axiom_dashboard help
-/

open MiniProver.Workbench

def demoFormulation : Formulation :=
  { id := "demo", stmt := True }

def demoStep : ReductionStep :=
  { name := "identity"
    src := demoFormulation
    dst := demoFormulation
    assumptions := Assumptions.empty
    skeleton := Skeleton.empty }

def usage : String :=
  String.intercalate "\n"
    [ "axiom_dashboard — Axiom Forge dashboard (deterministic text output)"
    , ""
    , "Usage:"
    , "  axiom_dashboard            # same as: all"
    , "  axiom_dashboard all"
    , "  axiom_dashboard reduction"
    , "  axiom_dashboard analytic"
    , "  axiom_dashboard help"
    ]

def runView (view : String) : IO UInt32 := do
  match view with
  | "all" =>
      IO.println (Dashboard.renderReduction demoStep)
      IO.println ""
      IO.println (Dashboard.renderAnalytic demoFormulation)
      pure 0
  | "reduction" =>
      IO.println (Dashboard.renderReduction demoStep)
      pure 0
  | "analytic" =>
      IO.println (Dashboard.renderAnalytic demoFormulation)
      pure 0
  | "help" =>
      IO.println usage
      pure 0
  | _ =>
      IO.println s!"Unknown view: {view}\n"
      IO.println usage
      pure 2

-- IMPORTANT:
-- Lake passes CLI arguments directly to `main`
def main (args : List String) : IO UInt32 := do
  match args with
  | []        => runView "all"
  | view :: _ => runView view
