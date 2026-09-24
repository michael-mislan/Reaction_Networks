import proofs.ProductiveMemory.ExtractionCellSpatial
import proofs.ProductiveMemory.ExtractionPopulationPotential

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition Set
noncomputable section
set_option Elab.async false

theorem extraction_spatial_pair_reset (N : ℕ) (hlarge : (200000000000000000000:ℝ) ≤ N)
    (rho zL zH : ℝ) (tag : Bool) (n d : Counts)
    (hg : extractionCellEnergy rho zL zH ⟨tag,(d,N)⟩ < 4*readyLevel ∧
      extractionCellEnergy rho zL zH ⟨tag,((fun i => n i-d i),N)⟩ < 4*readyLevel) :
    extractionCellSpatial N rho zL zH ⟨tag,(d,N)⟩+
      extractionCellSpatial N rho zL zH ⟨tag,((fun i => n i-d i),N)⟩ ≤
      extractionCellSpatial N rho zL zH ⟨tag,(n,2*N)⟩ := by
  exact spatial_pair_reset N (by linarith) (extractionEnergy tag)
    (fun y => by linarith only [extraction_energy_lower tag y,normSq_nonneg y])
    (extractionCenter rho zL zH tag) n d hg

theorem extraction_spatial_division_barrier (N : ℕ) (rho zL zH : ℝ) (c : TaggedCell)
    (hm : c.compartment.2=2*N) (he : 2*readyLevel ≤ extractionCellEnergy rho zL zH c) :
    Real.exp (2*(N:ℝ)*localAlpha*readyLevel) ≤ extractionCellSpatial N rho zL zH c := by
  unfold extractionCellSpatial spatialWeight
  rw [hm]
  simp only [Nat.cast_mul,Nat.cast_ofNat,sub_self,mul_zero,Real.exp_zero,one_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left he (by unfold localAlpha; positivity : 0 ≤ (N:ℝ)*localAlpha)
  nlinarith only [h]

theorem extraction_cell_spatial_source (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (200000000000000000000:ℝ) ≤ N) (rho zL zH γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hsL : extractDrift rho 0 (lift rho zL) = 0) (hsH : extractDrift rho 0 (lift rho zH) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (Q Ω : ℕ) (hQ : Q ≤ Ω) (c : TaggedCell)
    (hm : N ≤ c.compartment.2) (hmmax : c.compartment.2 ≤ 2*N)
    (he : extractionCellEnergy rho zL zH c < outerLevel) :
    growingCompartmentGenerator rho (resourceCoefficient γ Q Ω)
      (fun d => extractionCellSpatial N rho zL zH ⟨c.high,d⟩) c.compartment ≤
      ((N:ℝ)*localAlpha*readyLevel/960)*(2*Real.exp ((N:ℝ)*localAlpha*readyLevel/2)) := by
  have hn : 0 ≤ ((N:ℝ)*localAlpha*readyLevel/960)/2*extractionCellSpatial N rho zL zH c := by
    exact mul_nonneg (by unfold localAlpha readyLevel outerLevel; positivity) (extraction_spatial_nonneg N rho zL zH c)
  cases hb : c.high with
  | false =>
    have h := low_extraction_resource_spatial rho zL γ hr hzL hsL hγ hγmax Q Ω hQ N hN hlarge
      c.compartment hm hmmax (by simpa [extractionCellEnergy,extractionEnergy,extractionCenter,hb] using he)
    simp only [extractionCellSpatial,extractionCellEnergy,extractionEnergy,extractionCenter,hb,Bool.false_eq_true,if_false] at hn ⊢
    unfold energyExponential at h
    change _ ≤ ((N:ℝ)*localAlpha*innerEnergy/960)*(2*Real.exp ((N:ℝ)*localAlpha*innerEnergy/2))
    simp only [readyLevel,outerLevel,innerEnergy,outerEnergy] at h hn ⊢
    linarith only [h,hn]
  | true =>
    have h := high_extraction_resource_spatial rho zH γ hr hzH hsH hγ hγmax Q Ω hQ N hN hlarge
      c.compartment hm hmmax (by simpa [extractionCellEnergy,extractionEnergy,extractionCenter,hb] using he)
    simp only [extractionCellSpatial,extractionCellEnergy,extractionEnergy,extractionCenter,hb,if_true] at hn ⊢
    unfold energyExponential at h
    change _ ≤ ((N:ℝ)*localAlpha*innerEnergy/960)*(2*Real.exp ((N:ℝ)*localAlpha*innerEnergy/2))
    simp only [readyLevel,outerLevel,innerEnergy,outerEnergy] at h hn ⊢
    linarith only [h,hn]

theorem productive_raw_spatial_bound (N M W0 J : ℕ) (hN : 1 ≤ N)
    (hlarge : (200000000000000000000:ℝ) ≤ N) (rho zL zH γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hsL : extractDrift rho 0 (lift rho zL) = 0) (hsH : extractDrift rho 0 (lift rho zH) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) :
    (∑ e : ProductiveEvent s.val, productiveRate rho γ (4*W0) s.val e*
      (productiveRawPotential (extractionCellSpatial N rho zL zH) s.val e-
        potentialSum (extractionCellSpatial N rho zL zH) s.val.population)) ≤
      8*(M:ℝ)*(((N:ℝ)*localAlpha*readyLevel/960)*(2*Real.exp ((N:ℝ)*localAlpha*readyLevel/2))) := by
  rw [productive_raw_generator_sum]
  have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s.val.population.live.length)))
    (fun i _ => extraction_cell_spatial_source N hN hlarge rho zL zH γ hr hzL hzH hsL hsH hγ hγmax
      s.val.population.resource (4*W0) hs.2.1 (selectedCell s.val.population i)
      (hs.2.2.2.2.1 _ (selected_mem s.val.population i)).1
      (hs.2.2.2.2.1 _ (selected_mem s.val.population i)).2.le
      (productive_active_energy N M W0 J rho zL zH s _ (selected_mem s.val.population i)))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  have hc : (s.val.population.live.length:ℝ) ≤ 8*(M:ℝ) := by
    exact_mod_cast productive_active_cell_count N M W0 J rho zL zH s
  exact hb.trans (mul_le_mul_of_nonneg_right hc (by unfold localAlpha readyLevel outerLevel; positivity))

end
end ProductiveMemory
