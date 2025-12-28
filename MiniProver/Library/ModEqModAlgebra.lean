import Mathlib
import MiniProver.Library.ModEqMod

namespace MiniProver.Library

/-- Computational closure: equal remainders stay equal after adding the same `c`. -/
theorem mod_eq_add_right (n a b c : Nat) :
    a % n = b % n → (a + c) % n = (b + c) % n := by
  intro h
  -- Convert remainder equality to ModEq using Step 1.
  have hab : Nat.ModEq n a b := (modeq_iff_modEq_mod n a b).2 h
  -- Use ModEq algebra, then convert back to remainder equality.
  have hac : Nat.ModEq n (a + c) (b + c) := hab.add_right c
  exact (modeq_iff_modEq_mod n (a + c) (b + c)).1 hac

/-- Computational closure: equal remainders stay equal after multiplying by the same `c`. -/
theorem mod_eq_mul_right (n a b c : Nat) :
    a % n = b % n → (a * c) % n = (b * c) % n := by
  intro h
  have hab : Nat.ModEq n a b := (modeq_iff_modEq_mod n a b).2 h
  have hac : Nat.ModEq n (a * c) (b * c) := hab.mul_right c
  exact (modeq_iff_modEq_mod n (a * c) (b * c)).1 hac

/-- Bridge test: remainder-equality view ⇒ relational view (addition). -/
theorem modeq_add_right_via_mod (n a b c : Nat) :
    Nat.ModEq n a b → Nat.ModEq n (a + c) (b + c) := by
  intro hab
  have hmod : a % n = b % n := (modeq_iff_modEq_mod n a b).1 hab
  have : (a + c) % n = (b + c) % n := mod_eq_add_right n a b c hmod
  exact (modeq_iff_modEq_mod n (a + c) (b + c)).2 this

/-- Bridge test: remainder-equality view ⇒ relational view (multiplication). -/
theorem modeq_mul_right_via_mod (n a b c : Nat) :
    Nat.ModEq n a b → Nat.ModEq n (a * c) (b * c) := by
  intro hab
  have hmod : a % n = b % n := (modeq_iff_modEq_mod n a b).1 hab
  have : (a * c) % n = (b * c) % n := mod_eq_mul_right n a b c hmod
  exact (modeq_iff_modEq_mod n (a * c) (b * c)).2 this

end MiniProver.Library
