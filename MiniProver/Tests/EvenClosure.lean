import MiniProver.Core

namespace MiniProver

/--
Phase 6 (controlled test): If `m` is even (in `MP_Even`), then `m * n` is even (in `MP_Even`).
Proof strategy: transport to mathlib `Even`, use a standard lemma, transport back.
-/
theorem mp_even_mul_right {m n : Nat} (hm : MP_Even m) : MP_Even (m * n) := by
  have hm' : Even m := (mp_even_iff_even m).1 hm
  -- mathlib: Even m -> Even (m * n)
  have hmn' : Even (m * n) := by
    -- evenness closed under multiplication
    exact hm'.mul_right n
  exact (mp_even_iff_even (m * n)).2 hmn'

end MiniProver
