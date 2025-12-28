/-
Phase 13 — Step 4: ModEq Workbench Lemma Pack (Stable API)

This module is the ONE stable import for commonly-used Nat.ModEq tools.
Later phases should import this, not the individual Tests modules.

Policy:
- No new math here.
- Only stable wrapper names around already-LOCKED theorems.
- Wrappers are implemented with `by simpa using ...` to preserve determinism.
-/

import MiniProver.Library.ModEqMod
import MiniProver.Library.ModEqModAlgebra
import MiniProver.Library.ModEqDvdBridge
import MiniProver.Library.ModEqCanonical
import MiniProver.Library.ModEqLinearForm

import MiniProver.Library.ModEqAddCancel
import MiniProver.Library.ModEqAddShift
import MiniProver.Library.ModEqMulCancelCoprime
import MiniProver.Library.ModEqCoprimeMulIff
import MiniProver.Library.ModEqChineseRemainderExists
import MiniProver.Library.ModEqChineseRemainderUnique


namespace MiniProver.Workbench
namespace ModEq

/-- Stable alias: computational view `a ≡ b [MOD n] ↔ a % n = b % n`. -/
theorem iff_modEq_mod (n a b : Nat) : Nat.ModEq n a b ↔ a % n = b % n := by
  simpa using MiniProver.Library.modeq_iff_modEq_mod n a b

/-- Stable alias: canonical representative `a ≡ a % n [MOD n]`. -/
theorem canonical (n a : Nat) : Nat.ModEq n a (a % n) := by
  simpa using MiniProver.Library.modeq_to_mod n a

/-- Stable alias: `a ≡ b [MOD n] → a % n = b % n`. -/
theorem canonical_unique (n a b : Nat) (h : Nat.ModEq n a b) : a % n = b % n := by
  -- underlying theorem has args (n a b) and returns implication
  simpa using (MiniProver.Library.modeq_canonical_unique n a b h)

/-- Stable alias: Int linear form `a ≡ b [MOD n] ↔ ∃ z, b = a + n*z` (in Int). -/
theorem iff_linear_int (n a b : Nat) :
    Nat.ModEq n a b ↔ ∃ z : Int, (b : Int) = (a : Int) + (n : Int) * z := by
  simpa using MiniProver.Library.modEq_iff_linear_int n a b

/-- Stable alias: add-right cancellation iff. -/
theorem add_right_cancel_iff (n a b c : Nat) :
    Nat.ModEq n (a + c) (b + c) ↔ Nat.ModEq n a b := by
  simpa using MiniProver.Library.modeq_add_right_cancel_iff n a b c

/-- Stable alias: add-shift normalization iff. -/
theorem add_shift_iff (n a b c : Nat) :
    Nat.ModEq n a b ↔ Nat.ModEq n (a + c) (b + c) := by
  simpa using MiniProver.Library.modeq_add_shift_iff n a b c

/-- Stable alias: scaled-modulus left cancel (requires `c ≠ 0`). -/
theorem mul_left_cancel_nonzero_scaled (m a b c : Nat) (hc : c ≠ 0) :
    Nat.ModEq (c * m) (c * a) (c * b) → Nat.ModEq m a b := by
  simpa using MiniProver.Library.modeq_mul_left_cancel_nonzero_scaled m a b c hc

/-- Stable alias: scaled-modulus right cancel (requires `c ≠ 0`). -/
theorem mul_right_cancel_nonzero_scaled (m a b c : Nat) (hc : c ≠ 0) :
    Nat.ModEq (m * c) (a * c) (b * c) → Nat.ModEq m a b := by
  simpa using MiniProver.Library.modeq_mul_right_cancel_nonzero_scaled m a b c hc

/-- Stable alias: coprime product modulus normalization. -/
theorem and_iff_mul {a b m n : Nat} (hmn : Nat.Coprime m n) :
    (Nat.ModEq m a b ∧ Nat.ModEq n a b) ↔ Nat.ModEq (m * n) a b := by
  simpa using MiniProver.Library.modeq_and_modeq_iff_modeq_mul (a := a) (b := b) (m := m) (n := n) hmn

/-- Stable alias: CRT existence (∃ k). -/
theorem crt_exists {n m a b : Nat} (co : Nat.Coprime n m) :
    ∃ k : Nat, Nat.ModEq n k a ∧ Nat.ModEq m k b := by
  simpa using MiniProver.Library.chineseRemainder_exists (n := n) (m := m) (a := a) (b := b) co

/-- Stable alias: CRT uniqueness mod `n*m`. -/
theorem crt_unique_modEq {n m a b z z' : Nat} (co : Nat.Coprime n m)
    (hz : Nat.ModEq n z a ∧ Nat.ModEq m z b)
    (hz' : Nat.ModEq n z' a ∧ Nat.ModEq m z' b) :
    Nat.ModEq (n * m) z z' := by
  rcases hz with ⟨hz1, hz2⟩
  rcases hz' with ⟨hz1', hz2'⟩
  -- underlying theorem is curried: co → hz1 → hz2 → hz1' → hz2' → ...
  -- underlying theorem is curried: co → hz1 → hz2 → hz1' → hz2' → ...
  simpa using (MiniProver.Library.chineseRemainder_unique_modEq co hz1 hz2 hz1' hz2')
end ModEq
end MiniProver.Workbench
