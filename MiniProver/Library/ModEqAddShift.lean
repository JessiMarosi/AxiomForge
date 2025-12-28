import MiniProver.Library.ModEqAddCancel

namespace MiniProver.Library

/--
Phase 12 — Step 2:
Add-shift equivalence (move the same term to both sides).
-/
theorem modeq_add_shift_iff (n a b c : Nat) :
    Nat.ModEq n a b ↔ Nat.ModEq n (a + c) (b + c) := by
  constructor
  · intro h
    exact h.add_right c
  · intro h
    exact (modeq_add_right_cancel_iff (n := n) (a := a) (b := b) (c := c)).1 h

end MiniProver.Library
