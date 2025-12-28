import Mathlib

namespace MiniProver.Library

theorem modeq_iff_modEq_mod (n a b : Nat) :
    Nat.ModEq n a b ↔ a % n = b % n := by
  rfl

end MiniProver.Library
