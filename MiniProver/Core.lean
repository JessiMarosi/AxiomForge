namespace MiniProver

/--
A local definition of evenness, deliberately namespaced
to avoid collision with mathlib's `Even`.
-/
def MP_Even (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

/--
A simple theorem: if `n = 2 * k`, then `n` is `MP_Even`.
This mirrors your original intent but avoids name clashes.
-/
theorem mp_even_of_mul_two (k : Nat) : MP_Even (2 * k) := by
  unfold MP_Even
  exact ⟨k, rfl⟩

end MiniProver
