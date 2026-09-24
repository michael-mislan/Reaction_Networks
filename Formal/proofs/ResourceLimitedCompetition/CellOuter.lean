import proofs.ResourceLimitedCompetition.CellSpatial

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

noncomputable def cellOuter (N : ℕ) (zL zH : ℝ) (c : TaggedCell) : ℝ :=
  Real.exp ((N : ℝ)*localAlpha*cellEnergy zL zH c)

theorem cellOuter_nonneg (N : ℕ) (zL zH : ℝ) (c : TaggedCell) :
    0 ≤ cellOuter N zL zH c := (Real.exp_pos _).le

theorem cellOuter_birth (N : ℕ) (zL zH : ℝ) (c : TaggedCell)
    (he : cellEnergy zL zH c < 4*innerEnergy) :
    cellOuter N zL zH c ≤ Real.exp (4*(N : ℝ)*localAlpha*innerEnergy) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left he.le
    (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
  nlinarith only [h]

theorem cellOuter_barrier (N : ℕ) (zL zH : ℝ) (c : TaggedCell)
    (he : outerEnergy ≤ cellEnergy zL zH c) :
    Real.exp ((N : ℝ)*localAlpha*outerEnergy) ≤ cellOuter N zL zH c := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left he (by unfold localAlpha; positivity)

theorem cellOuter_source_bound (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (Q Ω : ℕ) (hQ : Q ≤ Ω) (c : TaggedCell)
    (hm : N ≤ c.compartment.2) (he : cellEnergy zL zH c < outerEnergy) :
    compartmentGenerator (resourceCoefficient γ Q Ω)
      (fun d => cellOuter N zL zH ⟨c.high,d⟩) c.compartment ≤
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  have hneg : 0 ≤ ((N : ℝ)*localAlpha*innerEnergy/672)*cellOuter N zL zH c := by
    apply mul_nonneg
    · unfold localAlpha innerEnergy outerEnergy
      positivity
    · exact cellOuter_nonneg N zL zH c
  cases hb : c.high with
  | false =>
    have hlocal := low_resource_local_affine zL γ hzL hsL hγ hγmax Q Ω hQ N hN hlarge
      c.compartment hm (by simpa [cellEnergy,hb,outerEnergy] using he)
    simp only [cellOuter,cellEnergy,hb,Bool.false_eq_true,if_false] at hneg ⊢
    unfold lowExponential at hlocal
    linarith only [hlocal,hneg]
  | true =>
    have hlocal := high_resource_local_affine zH γ hzH hsH hγ hγmax Q Ω hQ N hN hlarge
      c.compartment hm (by simpa [cellEnergy,hb,outerEnergy] using he)
    simp only [cellOuter,cellEnergy,hb,if_true] at hneg ⊢
    unfold highExponential at hlocal
    linarith only [hlocal,hneg]

end ResourceLimitedCompetition
