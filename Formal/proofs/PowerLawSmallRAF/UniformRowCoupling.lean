import Mathlib

namespace PowerLawSmallRAF

open scoped BigOperators

noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Complete a smaller subset uniformly, or truncate a larger subset uniformly.
This is a conditional weight on the target subset, not a mean replacement. -/
def uniformRowCompletionKernel (d : Nat) (B T : Finset J) : ℝ :=
  if T.card = d then
    if B.card ≤ d then
      if B ⊆ T then (Nat.choose (Fintype.card J - B.card) (d - B.card) : ℝ)⁻¹ else 0
    else
      if T ⊆ B then (Nat.choose B.card d : ℝ)⁻¹ else 0
  else 0

theorem uniformRowCompletionKernel_nonneg (d : Nat) (B T : Finset J) :
    0 ≤ uniformRowCompletionKernel d B T := by
  unfold uniformRowCompletionKernel
  split_ifs <;> positivity

omit [DecidableEq J] in
theorem filter_univ_card_eq_powersetCard (d : Nat) :
    (Finset.univ.filter fun T : Finset J => T.card = d) =
      (Finset.univ : Finset J).powersetCard d := by
  ext T
  simp

theorem filter_powersetCard_subsets (T : Finset J) (d : Nat) :
    ((Finset.univ : Finset J).powersetCard d).filter (fun B => B ⊆ T) =
      T.powersetCard d := by
  ext B
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  tauto

theorem sum_uniformRowCompletionKernel (d : Nat) (hd : d ≤ Fintype.card J)
    (B : Finset J) : (∑ T : Finset J, uniformRowCompletionKernel d B T) = 1 := by
  unfold uniformRowCompletionKernel
  rw [← Finset.sum_filter, filter_univ_card_eq_powersetCard]
  by_cases hbd : B.card ≤ d
  · simp only [hbd, ↓reduceIte]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_filter_powersetCard_subset B Finset.univ d (Finset.subset_univ _) hbd]
    simp only [Finset.card_univ]
    have hpos : 0 < Nat.choose (Fintype.card J - B.card) (d - B.card) :=
      Nat.choose_pos (by omega)
    exact mul_inv_cancel₀ (by exact_mod_cast hpos.ne')
  · simp only [hbd, ↓reduceIte]
    rw [← Finset.sum_filter, filter_powersetCard_subsets]
    simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    have hpos : 0 < Nat.choose B.card d := Nat.choose_pos (by omega)
    exact mul_inv_cancel₀ (by exact_mod_cast hpos.ne')

/-- Summing one cardinality shell of inputs gives a constant column weight.
This is the exact finite combinatorial step behind the uniform target law. -/
theorem sum_shell_uniformRowCompletionKernel (d b : Nat)
    (hd : d ≤ Fintype.card J) (hb : b ≤ Fintype.card J)
    (T : Finset J) (hT : T.card = d) :
    (∑ B ∈ (Finset.univ : Finset J).powersetCard b, uniformRowCompletionKernel d B T) =
      (Nat.choose (Fintype.card J) b : ℝ) / Nat.choose (Fintype.card J) d := by
  have hden : (Nat.choose (Fintype.card J) d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hd).ne'
  by_cases hbd : b ≤ d
  · have heq : (∑ B ∈ (Finset.univ : Finset J).powersetCard b,
        uniformRowCompletionKernel d B T) =
        ∑ B ∈ (Finset.univ : Finset J).powersetCard b,
          if B ⊆ T then (Nat.choose (Fintype.card J - b) (d-b) : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      have hc := (Finset.mem_powersetCard.mp hB).2
      simp only [uniformRowCompletionKernel, hT, hc, hbd, ↓reduceIte]
    rw [heq, ← Finset.sum_filter, filter_powersetCard_subsets]
    simp only [Finset.sum_const, Finset.card_powersetCard, hT, nsmul_eq_mul]
    have hden' : (Nat.choose (Fintype.card J - b) (d-b) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : d-b ≤ Fintype.card J-b)).ne'
    rw [← div_eq_mul_inv]
    apply (div_eq_div_iff hden' hden).mpr
    have heq' : (Nat.choose (Fintype.card J) d : ℝ) * Nat.choose d b =
        (Nat.choose (Fintype.card J) b : ℝ) * Nat.choose (Fintype.card J-b) (d-b) := by
      exact_mod_cast (Nat.choose_mul (n := Fintype.card J) (k := d) hbd)
    nlinarith
  · have heq : (∑ B ∈ (Finset.univ : Finset J).powersetCard b,
        uniformRowCompletionKernel d B T) =
        ∑ B ∈ (Finset.univ : Finset J).powersetCard b,
          if T ⊆ B then (Nat.choose b d : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      have hc := (Finset.mem_powersetCard.mp hB).2
      simp only [uniformRowCompletionKernel, hT, hc, hbd, ↓reduceIte]
    rw [heq, ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_filter_powersetCard_subset T Finset.univ b (Finset.subset_univ _)
      (by omega)]
    simp only [Finset.card_univ, hT]
    have hden' : (Nat.choose b d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : d ≤ b)).ne'
    rw [← div_eq_mul_inv]
    apply (div_eq_div_iff hden' hden).mpr
    have heq' : (Nat.choose (Fintype.card J) b : ℝ) * Nat.choose b d =
        (Nat.choose (Fintype.card J) d : ℝ) * Nat.choose (Fintype.card J-d) (b-d) := by
      exact_mod_cast (Nat.choose_mul (n := Fintype.card J) (k := b) (by omega : d ≤ b))
    nlinarith

/-- Every normalized cardinality-only input law has the uniform d-subset
output marginal under the completion/truncation kernel. -/
theorem uniformRowCompletionKernel_radial_marginal
    (d : Nat) (hd : d ≤ Fintype.card J) (f : Nat → ℝ)
    (hnorm : (∑ B : Finset J, f B.card) = 1) (T : Finset J) (hT : T.card = d) :
    (∑ B : Finset J, f B.card * uniformRowCompletionKernel d B T) =
      (Nat.choose (Fintype.card J) d : ℝ)⁻¹ := by
  rw [← Finset.powerset_univ, Finset.sum_powerset]
  have hinner : ∀ b ∈ Finset.range (Fintype.card J+1),
      (∑ B ∈ (Finset.univ : Finset J).powersetCard b,
        f B.card * uniformRowCompletionKernel d B T) =
        f b * ((Nat.choose (Fintype.card J) b : ℝ) / Nat.choose (Fintype.card J) d) := by
    intro b hb
    calc
      _ = ∑ B ∈ (Finset.univ : Finset J).powersetCard b,
          f b * uniformRowCompletionKernel d B T := by
        apply Finset.sum_congr rfl
        intro B hB
        rw [(Finset.mem_powersetCard.mp hB).2]
      _ = _ := by
        rw [← Finset.mul_sum, sum_shell_uniformRowCompletionKernel d b hd
          (by have := Finset.mem_range.mp hb; omega) T hT]
  simp only [Finset.card_univ]
  rw [Finset.sum_congr rfl hinner]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card f] at hnorm
  simp only [Finset.card_univ, nsmul_eq_mul] at hnorm
  simp only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  have hnorm' : (∑ b ∈ Finset.range (Fintype.card J+1), f b * Nat.choose (Fintype.card J) b) = 1 := by
    simpa only [mul_comm] using hnorm
  rw [hnorm', one_mul]

end
end PowerLawSmallRAF
