import proofs.SerialTransferSelection.BatchOuterInitial
import proofs.SerialTransferSelection.BatchSpatialProbability
import proofs.SerialTransferSelection.BatchPartitionProbability

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal
noncomputable local instance ChemicalDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) := Classical.decEq _

noncomputable def phaseChemicalRawError (N : ℕ) (M t : ℝ) : ℝ :=
  let u := (N : ℝ)*localAlpha*innerEnergy
  let drift := t*(16*M*(u/672)*Real.exp (u/2))
  Real.exp (-(8*u))*(M*Real.exp u+14*M*Real.exp (4*u)+drift)+
    Real.exp (-(2*u))*(M*Real.exp u+drift)+7*M*partitionError N

theorem remove_exponential_barrier (a p B : ℝ) (h : Real.exp a*p ≤ B) :
    p ≤ Real.exp (-a)*B := by
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-a)).le
  have hc : Real.exp (-a)*(Real.exp a*p)=p := by
    rw [← mul_assoc,← Real.exp_add]
    simp
  rwa [hc] at hm

theorem phase_global_chemical_probability (N M W0 : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (phaseStoppedModel γ hγ (4*W0) N W0 zL zH
      (phaseActiveDomain N M W0 zL zH)).total x ≤ q)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH))
    (hready : PhaseReadyPopulation N M zL zH s.val) :
    let P := (phaseStoppedModel γ hγ (4*W0) N W0 zL zH
      (phaseActiveDomain N M W0 zL zH)).uniformize q hq hbound
    P.poissonized (q*t) (FiniteKernel.eventIndicator (phaseOuterFailureSet N W0 zL zH _)) (.inl s)+
      P.poissonized (q*t) (FiniteKernel.eventIndicator (phaseDivisionFailureSet N W0 zL zH _)) (.inl s)+
      P.poissonized (q*t) (FiniteKernel.eventIndicator (phasePartitionFailureSet N W0 zL zH _)) (.inl s) ≤
      phaseChemicalRawError N M t := by
  classical
  dsimp only
  have ho := phase_global_outer_failure_bound N M W0 hN hlarge zL zH γ hzL hzH hsL hsH hγ hγmax q t hq hbound s
  have hd := phase_global_division_failure_bound N M W0 hN hlarge zL zH γ hzL hzH hsL hsH hγ hγmax q t hq hbound s
  have hp := phase_global_partition_failure_bound γ hγ (4*W0) N M W0 (by omega) hW zL zH hzL hzH q t hq hbound s
  have ho' := remove_exponential_barrier _ _ _
    (ho.trans (add_le_add (phase_initial_outer_with_reserve N M zL zH s.val hready) le_rfl))
  have hd' := remove_exponential_barrier _ _ _
    (hd.trans (add_le_add (phase_initial_spatial_bound N M zL zH s.val hready) le_rfl))
  simp only [phasePartitionReserve,hready.2.1,Nat.cast_zero,sub_zero] at hp
  have h := add_le_add (add_le_add ho' hd') hp
  convert h using 1
  unfold phaseChemicalRawError
  ring

end SerialTransferSelection
