import Mathlib.Data.Nat.ModEq

namespace MiniProver.Library

/--
Phase 12 — Step 3:
Multiplicative cancellation with a nonzero gate (left),
for the *scaled modulus* `c * m`.
-/
theorem modeq_mul_left_cancel_nonzero_scaled (m a b c : Nat) (hc : c ≠ 0) :
    Nat.ModEq (c * m) (c * a) (c * b) → Nat.ModEq m a b := by
  intro h
  exact Nat.ModEq.mul_left_cancel' (a := a) (b := b) (m := m) (c := c) hc h

/--
Phase 12 — Step 3:
Multiplicative cancellation with a nonzero gate (right),
for the *scaled modulus* `m * c`.
-/
theorem modeq_mul_right_cancel_nonzero_scaled (m a b c : Nat) (hc : c ≠ 0) :
    Nat.ModEq (m * c) (a * c) (b * c) → Nat.ModEq m a b := by
  intro h
  exact Nat.ModEq.mul_right_cancel' (a := a) (b := b) (m := m) (c := c) hc h

end MiniProver.Library
