import Mathlib
import MiniProver.Library.ModEqMod

namespace MiniProver.Library

/--
Phase 11 (Step 4):
Canonical representative for a ModEq class.

Every `a` is congruent modulo `n` to its remainder `a % n`.
-/
theorem modeq_to_mod (n a : Nat) :
    Nat.ModEq n a (a % n) := by
  -- Use the Step 1 bridge: ModEq ↔ remainder equality.
  apply (modeq_iff_modEq_mod n a (a % n)).2
  -- Goal: a % n = (a % n) % n
  -- Lemma: (a % n) % n = a % n
  simpa using (Nat.mod_mod a n).symm

/--
Uniqueness of the canonical representative:
If `a` and `b` are ModEq, then their canonical remainders coincide.
-/
theorem modeq_canonical_unique (n a b : Nat) :
    Nat.ModEq n a b → a % n = b % n := by
  intro h
  exact (modeq_iff_modEq_mod n a b).1 h

end MiniProver.Library
