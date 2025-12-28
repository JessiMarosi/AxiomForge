import Mathlib.Data.Nat.ModEq

namespace MiniProver.Library

/--
Phase 12 — Step 5:
Chinese Remainder Theorem (existence form).
If n and m are coprime, then there exists k such that:
k ≡ a [MOD n] and k ≡ b [MOD m].
-/
theorem chineseRemainder_exists {n m a b : Nat} (co : Nat.Coprime n m) :
    ∃ k : Nat, Nat.ModEq n k a ∧ Nat.ModEq m k b := by
  -- mathlib returns a sigma/subtype {k // ...}; we unwrap it into ∃ k, ...
  refine ⟨(Nat.chineseRemainder co a b).1, ?_⟩
  exact (Nat.chineseRemainder co a b).2

end MiniProver.Library
