import proofs.ResourceLimitedCompetition.ChemicalBranchCombination

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal

noncomputable local instance ChemicalProbabilityDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem global_chemical_probability (N M : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH (activeDomain N M zL zH)).total x ≤ q)
    (s : ActiveState (activeDomain N M zL zH))
    (hlen : s.val.live.length=M) (hD : s.val.divisions=0)
    (hm : ∀ c ∈ s.val.live, c.compartment.2=N)
    (he : ∀ c ∈ s.val.live, cellEnergy zL zH c ≤ 4*innerEnergy) :
    let P := (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH (activeDomain N M zL zH)).uniformize q hq hbound
    P.poissonized (q*t) (FiniteKernel.eventIndicator (outerFailureSet N M zL zH _)) (.inl s)+
      P.poissonized (q*t) (FiniteKernel.eventIndicator (divisionFailureSet N M zL zH _)) (.inl s)+
      P.poissonized (q*t) (FiniteKernel.eventIndicator (partitionFailureSet N M zL zH _)) (.inl s) ≤
      chemicalRawError N M t := by
  classical
  dsimp only
  obtain ⟨hinitD,hinitO,hinitP⟩ := initial_chemical_potentials N M zL zH s.val hlen hD hm he
  have ho := global_outer_failure_bound N M hN hlarge zL zH γ hzL hzH hsL hsH hγ hγmax q t hq hbound s
  have hd := global_division_failure_bound N M hN hlarge zL zH γ hzL hzH hsL hsH hγ hγmax q t hq hbound s
  have hp := global_partition_failure_bound γ hγ (4*(N*M)) N M (by omega) zL zH hzL hzH q t hq hbound s
  have ho' := ho.trans (add_le_add hinitO le_rfl)
  have hd' := hd.trans (add_le_add hinitD le_rfl)
  rw [hinitP] at hp
  have heO : (N : ℝ)*localAlpha*outerEnergy=16*chemicalScale N := by
    unfold chemicalScale innerEnergy
    ring
  have heD : 2*(N : ℝ)*localAlpha*innerEnergy=2*chemicalScale N := by unfold chemicalScale; ring
  have heB : 4*(N : ℝ)*localAlpha*innerEnergy=4*chemicalScale N := by unfold chemicalScale; ring
  rw [heO,heB] at ho'
  rw [heD] at hd'
  unfold birthSpatialCeiling at hd'
  rw [heB] at hd'
  apply chemical_branch_combination N M t _ _ _ ho' hd'
  unfold partitionError at hp
  nlinarith only [hp]

end ResourceLimitedCompetition
