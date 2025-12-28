import MiniProver.Library.ModEqDvdBridge

namespace MiniProver.Library

theorem modEq_iff_linear_int (n a b : Nat) :
    Nat.ModEq n a b ↔ ∃ z : Int, (b : Int) = (a : Int) + (n : Int) * z := by
  constructor
  · intro h
    -- TODO: replace `modeq_iff_int_dvd_int_sub` with the actual lemma name from Step 3.
    have hdvd : (n : Int) ∣ (b : Int) - (a : Int) :=
      (modeq_iff_int_dvd_int_sub (n := n) (a := a) (b := b)).1 h
    rcases hdvd with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hz' := congrArg (fun t => t + (a : Int)) hz
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz'
  · rintro ⟨z, hz⟩
    have hsub : (b : Int) - (a : Int) = (n : Int) * z := by
      have hz' := congrArg (fun t => t - (a : Int)) hz
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz'
    have hdvd : (n : Int) ∣ (b : Int) - (a : Int) := ⟨z, hsub⟩
    exact (modeq_iff_int_dvd_int_sub (n := n) (a := a) (b := b)).2 hdvd

end MiniProver.Library
