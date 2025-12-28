import Mathlib

namespace MiniProver

/--
Phase 10 (ModEq basics): Congruence is preserved under addition.
If a ≡ b [MOD n], then a + c ≡ b + c [MOD n].
-/
theorem modeq_add_right {n a b c : Nat} (h : Nat.ModEq n a b) : Nat.ModEq n (a + c) (b + c) := by
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h.add_right c

end MiniProver
