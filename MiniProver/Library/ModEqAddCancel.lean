import MiniProver.Library.ModEqDvdBridge

namespace MiniProver.Library

/--
Phase 12 — Step 1:
Add-cancellation for Nat.ModEq.
-/
theorem modeq_add_right_cancel_iff (n a b c : Nat) :
    Nat.ModEq n (a + c) (b + c) ↔ Nat.ModEq n a b := by
  constructor
  · intro h
    -- Step 3 bridge: ModEq ↔ Int divisibility of subtraction
    have hdvd :
        (n : Int) ∣ ((b + c : Nat) : Int) - ((a + c : Nat) : Int) :=
      (modeq_iff_int_dvd_int_sub (n := n) (a := a + c) (b := b + c)).1 h

    -- Cancel +c inside Int
    have hdvd' : (n : Int) ∣ (b : Int) - (a : Int) := by
      simpa using hdvd

    exact (modeq_iff_int_dvd_int_sub (n := n) (a := a) (b := b)).2 hdvd'
  · intro h
    -- Closure under adding the same right term
    exact h.add_right c

end MiniProver.Library
