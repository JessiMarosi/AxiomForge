import Mathlib

namespace MiniProver

/--
A local definition of evenness, deliberately namespaced
to avoid collision with mathlib's `Even`.
-/
def MP_Even (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

/--
A local definition of oddness, deliberately namespaced
to avoid collision with mathlib's `Odd`.
-/
def MP_Odd (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k + 1

/--
Equivalence: local `MP_Odd` matches mathlib's `Odd`.
-/
theorem mp_odd_iff_odd (n : Nat) : MP_Odd n ↔ Odd n := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    -- `Odd n` is `∃ t, n = t + t + 1`
    -- and `two_mul k : 2 * k = k + k`
    simpa [MP_Odd, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    -- rewrite `k + k + 1` as `2 * k + 1`
    simpa [MP_Odd, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk

/--
A simple theorem: if `n = 2 * k`, then `n` is `MP_Even`.
-/
theorem mp_even_of_mul_two (k : Nat) : MP_Even (2 * k) := by
  unfold MP_Even
  exact ⟨k, rfl⟩

/--
Equivalence: local `MP_Even` matches mathlib's `Even`.
-/
theorem mp_even_iff_even (n : Nat) : MP_Even n ↔ Even n := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [MP_Even, two_mul] using hk
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [MP_Even, two_mul] using hk

/--
Wrapper lemma using mathlib: if `m` and `n` are even
(mathlib `Even`), then `m + n` is even.
-/
theorem even_add_of_even {m n : Nat} (hm : Even m) (hn : Even n) : Even (m + n) := by
  have h : Even (m + n) ↔ (Even m ↔ Even n) :=
    Nat.even_add (m := m) (n := n)
  exact (h.mpr) (Iff.intro (fun _ => hn) (fun _ => hm))

/--
Phase 3: Use the equivalence bridge to transport an `Even` proof
back into `MP_Even`.
-/
theorem mp_even_add_of_mp_even {m n : Nat}
    (hm : MP_Even m) (hn : MP_Even n) : MP_Even (m + n) := by
  have hm' : Even m := (mp_even_iff_even m).1 hm
  have hn' : Even n := (mp_even_iff_even n).1 hn
  have hsum : Even (m + n) :=
    even_add_of_even (m := m) (n := n) hm' hn'
  exact (mp_even_iff_even (m + n)).2 hsum
/--
Phase 7: Operational transport lemma.
If `m` is odd (local) and `n` is even (local), then `m + n` is odd (local).
-/
theorem mp_odd_add_of_mp_odd_mp_even {m n : Nat} (hm : MP_Odd m) (hn : MP_Even n) : MP_Odd (m + n) := by
  have hm' : Odd m := (mp_odd_iff_odd m).1 hm
  have hn' : Even n := (mp_even_iff_even n).1 hn
  have hsum : Odd (m + n) := hm'.add_even hn'
  exact (mp_odd_iff_odd (m + n)).2 hsum

end MiniProver

