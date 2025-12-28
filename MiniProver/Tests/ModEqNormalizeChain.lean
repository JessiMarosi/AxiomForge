import MiniProver.Workbench.ModEq

import MiniProver.Workbench.ModEq
namespace MiniProver.Tests

/--
Phase 13 — Step 1:
Chain congruences by normalizing to canonical remainders.
(No direct use of `Nat.ModEq.trans`.)
-/
theorem modeq_chain_via_mod (n a b c : Nat)
    (hab : Nat.ModEq n a b) (hbc : Nat.ModEq n b c) :
    Nat.ModEq n a c := by
  -- Normalize each congruence to equality of remainders.
  have hab' : a % n = b % n := MiniProver.Workbench.ModEq.canonical_unique (n := n) (a := a) (b := b) hab
  have hbc' : b % n = c % n := MiniProver.Workbench.ModEq.canonical_unique (n := n) (a := b) (b := c) hbc

  -- Chain equalities of remainders.
  have hac' : a % n = c % n := Eq.trans hab' hbc'

  -- Convert back to ModEq using the definitional bridge from Phase 11 Step 1.
  -- In this environment: Nat.ModEq n a c ↔ a % n = c % n is rfl.
  -- So we can `simpa` using hac'.
  simpa using hac'

end MiniProver.Tests
