import MiniProver.Core
import Mathlib

namespace MiniProver

/--
Phase 8 (mod-2 calibration): mathlib parity ↔ computation.
-/
theorem even_iff_mod2_eq_zero (n : Nat) : Even n ↔ n % 2 = 0 := by
  -- mathlib already provides this equivalence
    simpa using (Nat.even_iff (n := n))

/--
Lift to the local predicate via the Phase 2 bridge.
-/
theorem mp_even_iff_mod2_eq_zero (n : Nat) : MP_Even n ↔ n % 2 = 0 := by
  -- MP_Even n ↔ Even n ↔ n % 2 = 0
  simpa [mp_even_iff_even n] using (even_iff_mod2_eq_zero n)

end MiniProver
