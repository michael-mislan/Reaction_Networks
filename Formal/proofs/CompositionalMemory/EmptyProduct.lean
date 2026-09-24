import proofs.CompositionalMemory.EmptyModule

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

theorem word_nonempty_mass {k : ℕ} (n : Fin k → Counts) :
    (∑ d ∈ wordDraws n, wordDrawWeight n d*
      (if ∀ i, drawModule d i ≠ (fun _ => 0) then 1 else 0)) =
        ∏ i, (1-(1/2 : ℝ)^(∑ a, n i a)) := by
  classical
  rw [word_draw_regroup n (fun d => if ∀ i, d i ≠ (fun _ => 0) then 1 else 0)]
  have he (d : Fin k → Counts) :
      (∏ i, daughterWeight (n i) (d i))*(if ∀ i, d i ≠ (fun _ => 0) then 1 else 0) =
        ∏ i, daughterWeight (n i) (d i)*(if d i ≠ (fun _ => 0) then 1 else 0) := by
    rw [Finset.prod_mul_distrib,Fintype.prod_boole]
    by_cases h : ∀ i, d i ≠ (fun _ => 0) <;> simp [h]
  simp_rw [he]
  rw [← Finset.prod_univ_sum (fun i => daughterDraws (n i))
    (fun i d => daughterWeight (n i) d*(if d ≠ (fun _ => 0) then 1 else 0))]
  simp_rw [daughter_nonempty_mass]

theorem word_nonempty_cap {k : ℕ} (n : Fin k → Counts) (M : ℕ)
    (hcap : ∀ i, ∑ a, n i a ≤ M) :
    (∑ d ∈ wordDraws n, wordDrawWeight n d*
      (if ∀ i, drawModule d i ≠ (fun _ => 0) then 1 else 0)) ≤
        (1-(1/2 : ℝ)^M)^k := by
  rw [word_nonempty_mass]
  calc
    _ ≤ ∏ _i : Fin k, (1-(1/2 : ℝ)^M) := by
      apply Finset.prod_le_prod
      · intro i _
        exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
      · intro i _
        apply sub_le_sub_left
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hcap i)
    _ = _ := by simp

end CompositionalMemory
