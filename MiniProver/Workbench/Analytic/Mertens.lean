import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace MiniProver.Workbench.Analytic

/--
`Mertens n` is the summatory Möbius function:

`M(n) = ∑_{k=1..n} μ(k)`.

Notes / conventions:
- Domain is `Nat` (natural numbers).
- The sum is over the closed interval `[1, n]` using `Finset.Icc`.
- This is a *definition only* (no bounds, no RH content).
- A Real-valued or floor-cutoff version can be added later as a separate obligation if needed.
-/
noncomputable def Mertens (n : Nat) : Int :=
  Finset.sum (Finset.Icc 1 n) (fun k => ArithmeticFunction.moebius k)

end MiniProver.Workbench.Analytic
