import MiniProver.Core

namespace MiniProver

/--
Phase 4: Bridge module proof.
Demonstrates that Core exports can be imported and reused from a second file.
-/
theorem bridge_mp_even_add {m n : Nat} (hm : MP_Even m) (hn : MP_Even n) : MP_Even (m + n) := by
  exact mp_even_add_of_mp_even (m := m) (n := n) hm hn

end MiniProver
