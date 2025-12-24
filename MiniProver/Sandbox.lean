import Mathlib

namespace MiniProver

/-!
Axiom Forge — Sandbox

Calibration proofs only.
-/

/-- Natural numbers calibration: 0 < 1. -/
example : (0 : Nat) < 1 := by
  decide

/-- Real numbers calibration: 0 < 1 in ℝ. -/
example : (0 : ℝ) < 1 := by
  norm_num

/-- Complex numbers calibration: (0 : ℂ) + 1 = 1. -/
example : (0 : ℂ) + 1 = 1 := by
  simp

end MiniProver
