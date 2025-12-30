/-
Phase 25 — Guided interface / dashboard (Step 1)

Text-only, deterministic renderers for core Workbench objects.
No UI frameworks, no IO, no search, no automation.

All functions are pure and return `String` for audit-friendly logging.
-/

import MiniProver.Workbench.Failure
import MiniProver.Workbench.Assumptions
import MiniProver.Workbench.Skeleton
import MiniProver.Workbench.Reduction
import MiniProver.Workbench.Analytic

noncomputable section

namespace MiniProver.Workbench
namespace Dashboard

def renderFailureKind : FailureKind → String
  | .invalidInput      => "invalidInput"
  | .missingAssumption => "missingAssumption"
  | .missingObligation => "missingObligation"
  | .policyViolation   => "policyViolation"
  | .internalInvariant => "internalInvariant"

def renderFailure (f : Failure) : String :=
  let ctx := match f.context with
    | none   => ""
    | some s => s!" (context: {s})"
  s!"Failure[{renderFailureKind f.kind}]: {f.message}{ctx}"

def renderAssumption (a : Assumption) : String :=
  s!"- {a.name}"

def renderLedger (xs : AssumptionLedger) : String :=
  if xs.isEmpty then
    "(no assumptions)"
  else
    String.intercalate "\n" (xs.map renderAssumption)

def renderObligation (o : Obligation) : String :=
  s!"- {o.name}"

def renderSkeleton (s : ProofSkeleton) : String :=
  let a := renderLedger s.assumptions
  let o :=
    if s.obligations.isEmpty then
      "(no obligations)"
    else
      String.intercalate "\n" (s.obligations.map renderObligation)
  s!"Assumptions:\n{a}\n\nObligations:\n{o}"

def renderCompileResult (r : Except Failure ProofSkeleton) : String :=
  match r with
  | .ok sk    => "compile: OK\n\n" ++ renderSkeleton sk
  | .error f  => "compile: ERROR\n\n" ++ renderFailure f

def renderValidateResult (r : Except Failure Unit) : String :=
  match r with
  | .ok _     => "validate: OK"
  | .error f  => "validate: ERROR\n\n" ++ renderFailure f

def renderReduction (step : ReductionStep) : String :=
  let v := renderValidateResult (Reduction.validate step)
  let c := renderCompileResult (Reduction.compile step)
  s!"ReductionStep: {step.name}\n{v}\n\n{c}"

def renderAnalytic (f : Formulation) : String :=
  match Analytic.toNormalForm f with
  | .ok nf   => "analytic: OK\n\n" ++ nf.tag
  | .error e => "analytic: ERROR\n\n" ++ renderFailure e

end Dashboard
end MiniProver.Workbench
