import proofs.ResourceLimitedCompetition.PopulationPotential

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

noncomputable def cellSpatial (N : ℕ) (zL zH : ℝ) (c : TaggedCell) : ℝ :=
  spatialWeight (1/1000000000000000) N c.compartment.2*
    Real.exp ((N : ℝ)*localAlpha*cellEnergy zL zH c)

theorem cellSpatial_nonneg (N : ℕ) (zL zH : ℝ) (c : TaggedCell) :
    0 ≤ cellSpatial N zL zH c := by
  unfold cellSpatial spatialWeight
  positivity

theorem cellSpatial_pair_reset (N : ℕ)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH : ℝ) (tag : Bool) (n d : Counts)
    (hgood : cellEnergy zL zH ⟨tag,(d,N)⟩ < 4*innerEnergy ∧
      cellEnergy zL zH ⟨tag,((fun i => n i-d i),N)⟩ < 4*innerEnergy) :
    cellSpatial N zL zH ⟨tag,(d,N)⟩+cellSpatial N zL zH ⟨tag,((fun i => n i-d i),N)⟩ ≤
      cellSpatial N zL zH ⟨tag,(n,2*N)⟩ := by
  cases tag with
  | false =>
    exact spatial_pair_reset N hlarge lowEnergy
      (fun y => by linarith only [lowEnergy_lower y,normSq_nonneg y])
      (pointOfState (lift sourceRates zL)) n d hgood
  | true =>
    exact spatial_pair_reset N hlarge highEnergy
      (fun y => by linarith only [highEnergy_lower y,normSq_nonneg y])
      (pointOfState (lift sourceRates zH)) n d hgood

theorem cellSpatial_division_barrier (N : ℕ) (zL zH : ℝ) (c : TaggedCell)
    (hm : c.compartment.2=2*N) (he : 2*innerEnergy ≤ cellEnergy zL zH c) :
    Real.exp (2*(N : ℝ)*localAlpha*innerEnergy) ≤ cellSpatial N zL zH c := by
  unfold cellSpatial spatialWeight
  rw [hm]
  simp only [Nat.cast_mul,Nat.cast_ofNat,sub_self,mul_zero,Real.exp_zero,one_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left he
    (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
  nlinarith only [h]

theorem cellSpatial_source_bound (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (Q Ω : ℕ) (hQ : Q ≤ Ω) (c : TaggedCell)
    (hm : N ≤ c.compartment.2) (hmmax : c.compartment.2 ≤ 2*N)
    (he : cellEnergy zL zH c < outerEnergy) :
    compartmentGenerator (resourceCoefficient γ Q Ω)
      (fun d => cellSpatial N zL zH ⟨c.high,d⟩) c.compartment ≤
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  have hneg : 0 ≤ ((N : ℝ)*localAlpha*innerEnergy/672)/2*cellSpatial N zL zH c := by
    apply mul_nonneg
    · unfold localAlpha innerEnergy outerEnergy
      positivity
    · exact cellSpatial_nonneg N zL zH c
  cases hb : c.high with
  | false =>
    have hlocal := low_resource_spatial_bound zL γ hzL hsL hγ hγmax Q Ω hQ N hN hlarge
      c.compartment hm hmmax (by simpa [cellEnergy,hb,outerEnergy] using he)
    simp only [cellSpatial,cellEnergy,hb,Bool.false_eq_true,if_false] at hneg ⊢
    unfold lowExponential at hlocal
    linarith only [hlocal,hneg]
  | true =>
    have hlocal := high_resource_spatial_bound zH γ hzH hsH hγ hγmax Q Ω hQ N hN hlarge
      c.compartment hm hmmax (by simpa [cellEnergy,hb,outerEnergy] using he)
    simp only [cellSpatial,cellEnergy,hb,if_true] at hneg ⊢
    unfold highExponential at hlocal
    linarith only [hlocal,hneg]

end ResourceLimitedCompetition
