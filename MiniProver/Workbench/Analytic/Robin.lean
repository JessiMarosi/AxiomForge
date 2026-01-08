import Mathlib

namespace MiniProver.Workbench.Analytic

/-
Robin Inequality — σ(n) definition (P1-level).
Declarative only. No proofs.
-/

noncomputable def robinSigma (n : Nat) : Nat :=
  (Nat.divisors n).sum (fun d => d)

def robinThreshold (n : Nat) : Prop :=
  5041 ≤ n

noncomputable def eulerGamma : Real :=
  Real.eulerMascheroniConstant

end MiniProver.Workbench.Analytic
