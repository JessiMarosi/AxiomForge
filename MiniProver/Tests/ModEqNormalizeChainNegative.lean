import MiniProver.Tests.ModEqNormalizeChain
import MiniProver.Tests.Negative

namespace MiniProver.Tests

/--
Phase 13 — Step 2 (Negative):
Chaining congruences must NOT typecheck if the moduli differ.
We wrap the failing attempt in `fail_if_success` so the file still compiles.
-/
theorem negative_test_modeq_chain_wrong_modulus (n a b c : Nat)
    (hab : Nat.ModEq n a b) (hbc : Nat.ModEq (n + 1) b c) : True := by
  fail_if_success
    have : Nat.ModEq n a c := by
      exact modeq_chain_via_mod (n := n) (a := a) (b := b) (c := c) hab hbc
  trivial

end MiniProver.Tests
