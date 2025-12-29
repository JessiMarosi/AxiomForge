import Mathlib

namespace MiniProver.Workbench.Analytic

/-- Canonical normal forms for analytic obligations (v0: Big-O only). -/
inductive NormalForm : Type where
  /-- Represents: ∃C>0, ∃x0>0, ∀x≥x0, |f x - g x| ≤ C * h x -/
  | bigO (f g h : Real → Real) : NormalForm


/-- Structured errors for deterministic normalization. -/
inductive NormalFormError : Type where
  | unsupportedShape (tag : String)
  | unsupportedFunction (name : String)
  | mixedDomains (detail : String)
  | missingSideCondition (detail : String)
  | notImplemented (detail : String)


/-- Stable, grep-friendly rendering for dashboard artifacts. -/
def NormalForm.render : NormalForm → String
  | .bigO _ _ _ =>
      "NF_BigO(Real): ∃C>0 ∃x0>0 ∀x≥x0, |f-g| ≤ C*h"

def NormalFormError.render : NormalFormError → String
  | .unsupportedShape t      => s!"ERR_UnsupportedShape({t})"
  | .unsupportedFunction n   => s!"ERR_UnsupportedFunction({n})"
  | .mixedDomains d          => s!"ERR_MixedDomains({d})"
  | .missingSideCondition d  => s!"ERR_MissingSideCondition({d})"
  | .notImplemented d        => s!"ERR_NotImplemented({d})"

/-- P0 entrypoint (structured): caller supplies f, g, h directly. -/
def toNormalFormP0 (f g h : Real → Real) : Except NormalFormError NormalForm :=
  Except.ok (.bigO f g h)

end MiniProver.Workbench.Analytic
