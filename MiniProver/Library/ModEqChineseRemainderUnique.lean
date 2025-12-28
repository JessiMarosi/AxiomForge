import Mathlib.Data.Nat.ModEq

namespace MiniProver.Library

/--
Phase 12 — Step 6:
Chinese Remainder uniqueness up to congruence mod (n*m).

If z and z' both satisfy:
  z ≡ a [MOD n] and z ≡ b [MOD m]
  z' ≡ a [MOD n] and z' ≡ b [MOD m]
then z ≡ z' [MOD n*m].
-/
theorem chineseRemainder_unique_modEq {n m a b z z' : Nat} (co : Nat.Coprime n m)
    (hzan : Nat.ModEq n z a) (hzbm : Nat.ModEq m z b)
    (hz'an : Nat.ModEq n z' a) (hz'bm : Nat.ModEq m z' b) :
    Nat.ModEq (n * m) z z' := by
  -- Both z and z' are congruent to the canonical chineseRemainder solution mod n*m.
  have hz  : Nat.ModEq (n * m) z  (Nat.chineseRemainder co a b) :=
    Nat.chineseRemainder_modEq_unique (n := n) (m := m) (co := co)
      (a := a) (b := b) (z := z) hzan hzbm
  have hz' : Nat.ModEq (n * m) z' (Nat.chineseRemainder co a b) :=
    Nat.chineseRemainder_modEq_unique (n := n) (m := m) (co := co)
      (a := a) (b := b) (z := z') hz'an hz'bm
  -- Conclude z ≡ z' by transitivity/symmetry.
  exact hz.trans hz'.symm

end MiniProver.Library
