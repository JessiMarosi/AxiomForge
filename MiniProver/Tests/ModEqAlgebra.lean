import Mathlib

namespace MiniProver

/--
Phase 10 (ModEq algebra): reflexivity.
-/
theorem modeq_refl (n a : Nat) : Nat.ModEq n a a :=
  Nat.ModEq.refl a

/--
Phase 10 (ModEq algebra): symmetry.
-/
theorem modeq_symm {n a b : Nat} (h : Nat.ModEq n a b) : Nat.ModEq n b a :=
  h.symm

/--
Phase 10 (ModEq algebra): transitivity.
-/
theorem modeq_trans {n a b c : Nat}
    (h₁ : Nat.ModEq n a b) (h₂ : Nat.ModEq n b c) : Nat.ModEq n a c :=
  h₁.trans h₂

end MiniProver
