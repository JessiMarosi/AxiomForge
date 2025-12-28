import MiniProver.Core
import Mathlib

namespace MiniProver

/--
Phase 9 (mod-2 calibration): mathlib odd ↔ computation.
-/
theorem odd_iff_mod2_eq_one (n : Nat) : Odd n ↔ n % 2 = 1 := by
  -- mathlib already provides this equivalence
  simpa using (Nat.odd_iff (n := n))

/--
Lift to the local predicate via the Phase 7 bridge.
-/
theorem mp_odd_iff_mod2_eq_one (n : Nat) : MP_Odd n ↔ n % 2 = 1 := by
  -- MP_Odd n ↔ Odd n ↔ n % 2 = 1
  simpa [mp_odd_iff_odd n] using (odd_iff_mod2_eq_one n)

end MiniProver
