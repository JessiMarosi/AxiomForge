import Mathlib

namespace MiniProver

/--
Phase 10 (ModEq basics): Congruence is preserved under multiplication.
If a ≡ b [MOD n], then a * c ≡ b * c [MOD n].
-/
theorem modeq_mul_right {n a b c : Nat} (h : Nat.ModEq n a b) : Nat.ModEq n (a * c) (b * c) := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.mul_right c

end MiniProver
