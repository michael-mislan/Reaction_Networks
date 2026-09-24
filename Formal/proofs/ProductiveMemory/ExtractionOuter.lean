import proofs.ProductiveMemory.ExtractionSpatialBoundary

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition Set
noncomputable section
set_option Elab.async false

def extractionCellOuter (N : ℕ) (rho zL zH : ℝ) (c : TaggedCell) : ℝ :=
  Real.exp ((N:ℝ)*localAlpha*extractionCellEnergy rho zL zH c)

theorem extraction_outer_nonneg (N : ℕ) (rho zL zH : ℝ) (c : TaggedCell) :
    0 ≤ extractionCellOuter N rho zL zH c := (Real.exp_pos _).le

theorem extraction_outer_birth (N : ℕ) (rho zL zH : ℝ) (c : TaggedCell)
    (he : extractionCellEnergy rho zL zH c < 4*readyLevel) :
    extractionCellOuter N rho zL zH c ≤ Real.exp (4*(N:ℝ)*localAlpha*readyLevel) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left he.le (by unfold localAlpha; positivity : 0 ≤ (N:ℝ)*localAlpha)
  nlinarith only [h]

theorem extraction_outer_barrier (N : ℕ) (rho zL zH : ℝ) (c : TaggedCell)
    (he : 8*readyLevel ≤ extractionCellEnergy rho zL zH c) :
    Real.exp ((N:ℝ)*localAlpha*(8*readyLevel)) ≤ extractionCellOuter N rho zL zH c := by
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he (by unfold localAlpha; positivity))

def productiveOuterReserve (N M D : ℕ) : ℝ :=
  (14*(M:ℝ)-2*(D:ℝ))*Real.exp (4*(N:ℝ)*localAlpha*readyLevel)

theorem productive_outer_reserve_nonneg (N M D : ℕ) (hD : D ≤ 7*M) :
    0 ≤ productiveOuterReserve N M D := by
  have hd : (D:ℝ) ≤ 7*(M:ℝ) := by exact_mod_cast hD
  exact mul_nonneg (by linarith) (Real.exp_pos _).le

theorem extraction_outer_source (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (200000000000000000000:ℝ) ≤ N) (rho zL zH γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hsL : extractDrift rho 0 (lift rho zL) = 0) (hsH : extractDrift rho 0 (lift rho zH) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (Q Ω : ℕ) (hQ : Q ≤ Ω) (c : TaggedCell) (hm : N ≤ c.compartment.2)
    (he : extractionCellEnergy rho zL zH c < outerLevel) :
    growingCompartmentGenerator rho (resourceCoefficient γ Q Ω)
      (fun d => extractionCellOuter N rho zL zH ⟨c.high,d⟩) c.compartment ≤
      ((N:ℝ)*localAlpha*readyLevel/960)*(2*Real.exp ((N:ℝ)*localAlpha*readyLevel/2)) := by
  obtain ⟨hb,hbmax⟩ := resource_coefficient_bounds γ Q Ω hγ hQ
  have hn : 0 ≤ ((N:ℝ)*localAlpha*readyLevel/960)*extractionCellOuter N rho zL zH c := by
    exact mul_nonneg (by unfold localAlpha readyLevel outerLevel; positivity) (extraction_outer_nonneg N rho zL zH c)
  cases ht : c.high with
  | false =>
    have h := low_extraction_growth_affine rho zL _ hr hzL hsL hb (hbmax.trans hγmax) N hN hlarge c.compartment hm
      (by simpa [extractionCellEnergy,extractionEnergy,extractionCenter,ht] using he)
    simp only [extractionCellOuter,extractionCellEnergy,extractionEnergy,extractionCenter,ht,Bool.false_eq_true,if_false] at hn ⊢
    unfold energyExponential at h
    simp only [readyLevel,outerLevel,innerEnergy,outerEnergy] at h hn ⊢
    linarith only [h,hn]
  | true =>
    have h := high_extraction_growth_affine rho zH _ hr hzH hsH hb (hbmax.trans hγmax) N hN hlarge c.compartment hm
      (by simpa [extractionCellEnergy,extractionEnergy,extractionCenter,ht] using he)
    simp only [extractionCellOuter,extractionCellEnergy,extractionEnergy,extractionCenter,ht,if_true] at hn ⊢
    unfold energyExponential at h
    simp only [readyLevel,outerLevel,innerEnergy,outerEnergy] at h hn ⊢
    linarith only [h,hn]

end
end ProductiveMemory
