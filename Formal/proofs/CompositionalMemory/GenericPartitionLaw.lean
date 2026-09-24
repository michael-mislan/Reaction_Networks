import proofs.HeritableCompositions.PartitionTail

namespace CompositionalMemory
open HeritableCompositions

abbrev GeneralDraw (k d : ℕ) := Fin k × Fin d → ℕ

noncomputable def generalDraws {k d : ℕ} (n : Fin k → Fin d → ℕ) : Finset (GeneralDraw k d) :=
  Fintype.piFinset (fun i => Finset.range (n i.1 i.2+1))

noncomputable def generalDrawWeight {k d : ℕ} (n : Fin k → Fin d → ℕ) (x : GeneralDraw k d) : ℝ :=
  ∏ i, fairBinomialWeight (n i.1 i.2) (x i)

theorem general_draw_weight_nonneg {k d : ℕ} (n : Fin k → Fin d → ℕ) (x : GeneralDraw k d) :
    0 ≤ generalDrawWeight n x := Finset.prod_nonneg (fun _ _ => fairBinomialWeight_nonneg _ _)

theorem general_draw_weight_sum {k d : ℕ} (n : Fin k → Fin d → ℕ) :
    ∑ x ∈ generalDraws n, generalDrawWeight n x=1 :=
  product_weight_sum (fun i : Fin k × Fin d => Finset.range (n i.1 i.2+1))
    (fun i a => fairBinomialWeight (n i.1 i.2) a) (fun i => fair_binomial_sum (n i.1 i.2))

theorem general_draw_marginal {k d : ℕ} (n : Fin k → Fin d → ℕ) (i : Fin k × Fin d) (g : ℕ → ℝ) :
    ∑ x ∈ generalDraws n, generalDrawWeight n x*g (x i)=
      ∑ a ∈ Finset.range (n i.1 i.2+1), fairBinomialWeight (n i.1 i.2) a*g a :=
  product_weight_marginal (fun j : Fin k × Fin d => Finset.range (n j.1 j.2+1))
    (fun j a => fairBinomialWeight (n j.1 j.2) a) (fun j => fair_binomial_sum (n j.1 j.2)) i g

theorem general_binomial_volume_tail (n N : ℕ) (hN : 0 < N) (C δ : ℝ)
    (hC : 0 < C) (hδ : 0 < δ) (hn : (n:ℝ) ≤ C*(N:ℝ)) :
    (∑ x ∈ Finset.range (n+1), if (N:ℝ)*δ ≤ |(x:ℝ)-(n:ℝ)/2| then fairBinomialWeight n x else 0) ≤
      2*Real.exp (-2*(N:ℝ)*δ^2/C) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  by_cases hn0 : n=0
  · subst n
    have hd : ¬ (N:ℝ)*δ ≤ 0 := not_le.mpr (mul_pos hNr hδ)
    simp [hd]
    positivity
  · have hnr : (0:ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    apply (fair_binomial_two_sided_tail n (Nat.pos_of_ne_zero hn0) ((N:ℝ)*δ) (by positivity)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ hnr hC).mpr
    have hh := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (N:ℝ)*δ^2)
    nlinarith only [hh]

/-- One joint allocation, with a linear union factor in module/species count.
Sibling allocations are complementary rather than independent. -/
theorem general_draw_joint_tail {k d : ℕ} (n : Fin k → Fin d → ℕ) (N : ℕ) (hN : 0 < N)
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) (hn : ∀ i a, (n i a:ℝ) ≤ C*(N:ℝ)) :
    (∑ x ∈ generalDraws n, generalDrawWeight n x*
      (if ∃ i : Fin k × Fin d, (N:ℝ)*δ ≤ |(x i:ℝ)-(n i.1 i.2:ℝ)/2| then 1 else 0)) ≤
      2*(k:ℝ)*(d:ℝ)*Real.exp (-2*(N:ℝ)*δ^2/C) := by
  classical
  have h := weighted_union_bound (generalDraws n) (generalDrawWeight n)
    (fun x _ => general_draw_weight_nonneg n x)
    (fun i x => (N:ℝ)*δ ≤ |(x i:ℝ)-(n i.1 i.2:ℝ)/2|)
  have hm (i : Fin k × Fin d) :
      (∑ x ∈ generalDraws n, generalDrawWeight n x*
        (if (N:ℝ)*δ ≤ |(x i:ℝ)-(n i.1 i.2:ℝ)/2| then 1 else 0)) ≤
      2*Real.exp (-2*(N:ℝ)*δ^2/C) := by
    rw [general_draw_marginal n i (fun a => if (N:ℝ)*δ ≤ |(a:ℝ)-(n i.1 i.2:ℝ)/2| then 1 else 0)]
    simpa only [mul_ite,mul_one,mul_zero] using general_binomial_volume_tail (n i.1 i.2) N hN C δ hC hδ (hn i.1 i.2)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hm i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul] at hs
  apply h.trans
  nlinarith only [hs]

end CompositionalMemory
