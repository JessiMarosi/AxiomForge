import Mathlib

namespace MiniProver.Library

/--
Phase 11 (Step 3):
Arithmetic (dvd) view of modular equivalence.

In this mathlib version, the canonical lemma characterizes Nat.ModEq via
divisibility in ℤ of the integer difference.
-/
theorem modeq_iff_int_dvd_int_sub (n a b : Nat) :
    Nat.ModEq n a b ↔ (n : Int) ∣ (b : Int) - (a : Int) := by
  -- `Nat.modEq_iff_dvd` already has the right shape with implicit arguments.
  -- We just `simpa` to match our explicit statement.
  simpa using (Nat.modEq_iff_dvd (n := n) (a := a) (b := b))

end MiniProver.Library
