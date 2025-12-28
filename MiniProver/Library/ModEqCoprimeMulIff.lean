import Mathlib.Data.Nat.ModEq

namespace MiniProver.Library

/--
Phase 12 — Step 4:
If m and n are coprime, then congruence mod m and mod n
is equivalent to congruence mod (m*n).
-/
theorem modeq_and_modeq_iff_modeq_mul {a b m n : Nat} (hmn : Nat.Coprime m n) :
    (Nat.ModEq m a b ∧ Nat.ModEq n a b) ↔ Nat.ModEq (m * n) a b := by
  simpa using (Nat.modEq_and_modEq_iff_modEq_mul (a := a) (b := b) (m := m) (n := n) hmn)

end MiniProver.Library
