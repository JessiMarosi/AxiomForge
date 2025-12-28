import MiniProver.Core
import Mathlib.Tactic

namespace MiniProver

/--
Phase 6 (negative test): Attempting to prove `MP_Even 1` should fail.
We wrap the attempt in `fail_if_success` so the file still compiles.
-/
theorem negative_test_mp_even_one : True := by
  fail_if_success
    have : MP_Even 1 := by
      unfold MP_Even
      refine ⟨0, ?_⟩
      simp
  trivial

end MiniProver
