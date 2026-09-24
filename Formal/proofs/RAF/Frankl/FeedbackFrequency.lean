import proofs.RAF.Frankl.FeedbackDefect

namespace RAF.Frankl
open RAF RAFQueryCompilation
open scoped Classical

variable {M R : Type*} [DecidableEq M] [Fintype M] [Fintype R] [DecidableEq R]

/-- Exact integer form of the guide's ceiling lower bound. Dividing by the
positive quantity 2*|U| gives f(r) >= ceil((M-|D|)/2 + I_D/|U|). -/
theorem feedback_defect_frequency (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (E : Finset R)
    (hE : ∀ r ∈ E, SeedReaction Q r) (hne : (evaluate Q C E).Nonempty) :
    ∃ r ∈ evaluate Q C E,
      (evaluate Q C E).card * ((fixedFamily Q C).card - (badProjectionFamily Q C E).card) +
        2 * ∑ W ∈ badProjectionFamily Q C E, (W ∩ evaluate Q C E).card ≤
      (evaluate Q C E).card *
        (2 * ((fixedFamily Q C).filter (fun W => r ∈ W)).card) := by
  let F := fixedFamily Q C
  let U := evaluate Q C E
  let f := fun r : R => (F.filter (fun W => r ∈ W)).card
  obtain ⟨r,hr,hm⟩ := Finset.exists_max_image U f hne
  refine ⟨r,hr,?_⟩
  have hi : (∑ W ∈ F, (W ∩ U).card) = ∑ r ∈ U, f r := by
    calc
      _ = ∑ W ∈ F, ∑ r ∈ U, if r ∈ W then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro W _
        simp [Finset.inter_comm]
      _ = ∑ r ∈ U, ∑ W ∈ F, if r ∈ W then 1 else 0 := Finset.sum_comm
      _ = _ := by simp [f]
  have hs : (∑ q ∈ U, f q) ≤ U.card * f r := by
    simpa using Finset.sum_le_sum (fun q hq => hm q hq)
  have hb := feedback_defect_bound Q C E hE hne
  change U.card * (F.card - (badProjectionFamily Q C E).card) +
    2 * ∑ W ∈ badProjectionFamily Q C E, (W ∩ U).card ≤ 2 * ∑ W ∈ F, (W ∩ U).card at hb
  rw [hi] at hb
  have hs2 := Nat.mul_le_mul_left 2 hs
  exact le_trans hb (by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hs2)

end RAF.Frankl
