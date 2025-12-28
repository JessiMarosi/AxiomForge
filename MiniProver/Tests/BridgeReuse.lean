import MiniProver.Bridge

namespace MiniProver

/--
Phase 6 (controlled test): Reuse the Bridge module from a test file.
Demonstrates multi-module proof reuse: Tests -> Bridge -> Core.
-/
theorem test_bridge_add {m n : Nat} (hm : MP_Even m) (hn : MP_Even n) : MP_Even (m + n) := by
  exact bridge_mp_even_add (m := m) (n := n) hm hn

end MiniProver
