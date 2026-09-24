import proofs.RandomViability.QuietPathComparison

namespace RandomViability
open Classical FiniteCopy
noncomputable section
namespace FiniteLabeledKernel
variable {α β : Type*} [Fintype β]

/-- The first marked reaction is the target; neutral labels may intervene. -/
def firstRace (marked target : β → Prop) : (n : ℕ) → RewardPath β n → Prop
  | 0, _ => False
  | n+1, p => if marked p.1 then target p.1 else firstRace marked target n p.2

theorem firstRace_mass_succ (K : FiniteLabeledKernel α β) (marked target : β → Prop)
    (n : ℕ) (x : α) :
    K.pathEventMass (n+1) x (firstRace marked target (n+1)) =
      ∑ b, K.prob x b * (if marked b then (if target b then 1 else 0) else
        K.pathEventMass n (K.next x b) (firstRace marked target n)) := by
  change (∑ p : β × RewardPath β n, if firstRace marked target (n+1) p then
    K.prob x p.1*K.pathWeight n (K.next x p.1) p.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hm : marked b
  · by_cases ht : target b
    · simp only [firstRace, if_pos hm, if_pos ht, ← Finset.mul_sum, K.pathWeight_sum, mul_one]
    · simp only [firstRace, if_pos hm, if_neg ht, Finset.sum_const_zero, mul_zero]
  · simp only [firstRace, if_neg hm, pathEventMass, Finset.mul_sum, mul_ite, mul_zero]

theorem firstRace_mass_lower (K : FiniteLabeledKernel α β) (marked target : β → Prop)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1)
    (htarget : ∀ x, a ≤ ∑ z, if marked z ∧ target z then K.prob x z else 0)
    (hmarked : ∀ x, (∑ z, if marked z then K.prob x z else 0) ≤ b)
    (n : ℕ) (x : α) :
    a/b*(1-(1-b)^n) ≤ K.pathEventMass n x (firstRace marked target n) := by
  induction n generalizing x with
  | zero => simp [pathEventMass, firstRace]
  | succ n ih =>
    let L := a/b*(1-(1-b)^n)
    have hL : 0 ≤ L := mul_nonneg (div_nonneg ha hb.le)
      (sub_nonneg.mpr (pow_le_one₀ (by linarith) (by linarith)))
    have hsplit : (∑ z, if ¬ marked z then K.prob x z else 0) =
        1-(∑ z, if marked z then K.prob x z else 0) := by
      have hh : (∑ z, if ¬ marked z then K.prob x z else 0) +
          (∑ z, if marked z then K.prob x z else 0) = 1 := by
        rw [← Finset.sum_add_distrib, ← K.row_sum x]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : marked z <;> simp [hz]
      linarith
    have hn : 1-b ≤ ∑ z, if ¬ marked z then K.prob x z else 0 := by
      rw [hsplit]
      linarith [hmarked x]
    have hlower : a+(1-b)*L ≤ K.pathEventMass (n+1) x (firstRace marked target (n+1)) := by
      rw [firstRace_mass_succ]
      calc
        _ ≤ (∑ z, if marked z ∧ target z then K.prob x z else 0) +
            (∑ z, if ¬ marked z then K.prob x z else 0)*L :=
          add_le_add (htarget x) (mul_le_mul_of_nonneg_right hn hL)
        _ = ∑ z, ((if marked z ∧ target z then K.prob x z else 0) +
            (if ¬ marked z then K.prob x z else 0)*L) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro z _
          by_cases hm : marked z
          · by_cases ht : target z <;> simp [hm, ht]
          · simp only [hm, false_and, if_false, not_false_eq_true, if_true, zero_add]
            exact mul_le_mul_of_nonneg_left (ih (K.next x z)) (K.nonneg x z)
    have he : a/b*(1-(1-b)^(n+1)) = a+(1-b)*L := by
      dsimp [L]
      rw [pow_succ]
      field_simp
      ring
    rw [he]
    exact hlower

end FiniteLabeledKernel
end
end RandomViability
