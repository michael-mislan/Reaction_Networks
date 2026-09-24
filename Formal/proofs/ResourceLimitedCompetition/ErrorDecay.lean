import proofs.ResourceLimitedCompetition.ChemicalTailScalar

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Filter
open scoped Topology

theorem nat_exponential_decay (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.exp (-c*(N : ℝ))) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hn.const_mul_atTop hc)
  simpa only [Function.comp_def,neg_mul] using h

theorem competition_error_tendsto_zero (M : ℕ) (γ : ℝ) :
    Tendsto (fun N : ℕ => competitionError N M γ) atTop (𝓝 0) := by
  have hc : 0 < localAlpha*innerEnergy/2 := by norm_num [localAlpha,innerEnergy,outerEnergy]
  have hC : Tendsto (fun N : ℕ => Real.exp (-chemicalScale N/2)) atTop (𝓝 0) := by
    convert nat_exponential_decay (localAlpha*innerEnergy/2) hc using 1
    funext N
    congr 1
    unfold chemicalScale
    ring
  have hO : Tendsto (fun N : ℕ => Real.exp (-(19*(N : ℝ)/500000))) atTop (𝓝 0) := by
    convert nat_exponential_decay (19/500000) (by norm_num) using 1
    funext N
    congr 1
    ring
  have hD : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)/2500)) atTop (𝓝 0) := by
    convert nat_exponential_decay (1/2500) (by norm_num) using 1
    funext N
    congr 1
    ring
  have h := ((hC.const_mul ((M : ℝ)*(32+4/(21*γ)))).add hO).add hD
  simpa only [competitionError,chemicalErrorBound,mul_zero,add_zero] using h

theorem competition_error_nonneg (N M : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    0 ≤ competitionError N M γ := by
  unfold competitionError chemicalErrorBound
  positivity

theorem competition_error_threshold (M : ℕ) (γ ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 140000000000000000000 ≤ K ∧
      ∀ N : ℕ, K ≤ N → competitionError N M γ < ε := by
  have he : ∀ᶠ N : ℕ in atTop, competitionError N M γ < ε :=
    (tendsto_order.mp (competition_error_tendsto_zero M γ)).2 ε hε
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  refine ⟨max K 140000000000000000000,le_max_right _ _,?_⟩
  intro N hN
  exact hK N ((le_max_left _ _).trans hN)

end ResourceLimitedCompetition
