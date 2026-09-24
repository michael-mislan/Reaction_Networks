import proofs.SerialTransferSelection.ReadyPopulation
import proofs.SerialTransferSelection.CycleLawBounds

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

variable (M N J : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
  (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
  (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
  (tag : Fin M → Bool)
  (c : ∀ i, {c : Compartment // c ∈ recoveryCellDomain N zL zH (tag i)})
  (hv : ∀ i, N ≤ (c i).val.2 ∧ (c i).val.2 < 2*N)

def retainedServiceGoodSet : Set (∀ i, StoppedCompartment (recoveryCellDomain N zL zH (tag i)) × Fin (J+1)) :=
  {x | ∀ i, (x i).1 ∈ readyRecoverySet N (c i).val.2
    (recoveryCenter zL zH (tag i)) (recoveryEnergy (tag i)) ∧ (x i).2.val < J}

noncomputable def recoveryRestartOutput
    (x : ∀ i, StoppedCompartment (recoveryCellDomain N zL zH (tag i)) × Fin (J+1))
    (hx : x ∈ retainedServiceGoodSet M N J zL zH tag c) : ReadyPopulation N M zL zH :=
  ⟨recoveredRefill M N zL zH tag c (fun i => (x i).1),
    readyPopulation_mem N M hN zL zH hzL hzH _
      (recoveredRefill_ready M N zL zH tag c hv (fun i => (x i).1) (fun i => (hx i).1))⟩

noncomputable def recoveryRestartLaw (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ i x, (recoveryCellModel N zL zH (tag i)).total x ≤ q) :
    FiniteLaw (Option (ReadyPopulation N M zL zH)) :=
  guardedPush (retainedPopulationServiceLaw M N J zL zH tag q hq hclock c)
    (retainedServiceGoodSet M N J zL zH tag c)
    (recoveryRestartOutput M N J hN zL zH hzL hzH tag c hv)

def recoveryPreservesAncestry (s : ReadyPopulation N M zL zH) : Prop :=
  let original := List.ofFn (fun i => (⟨tag i,(c i).val⟩ : TaggedCell))
  ∀ b, ancestralCount b s.val.live=ancestralCount b original ∧
    ancestralMembrane b s.val.live=ancestralMembrane b original

theorem recoveryRestartLaw_probability
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (hJ : 0 < J)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ i x, (recoveryCellModel N zL zH (tag i)).total x ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (he : ∀ j, recoveryEnergy (tag j) (fun i => concentration (c j).val.2 (c j).val.1 i-
      recoveryCenter zL zH (tag j) i) ≤ 8*innerEnergy) :
    1-(M : ℝ)*(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*(q : ℝ)/J) ≤
      (recoveryRestartLaw M N J hN zL zH hzL hzH tag c hv q hq hclock).expect
        (FiniteKernel.eventIndicator (successfulOutput (recoveryPreservesAncestry M N zL zH tag c))) := by
  unfold recoveryRestartLaw
  rw [guardedPush_probability _ _ _ _ (by
    intro x hx b
    exact recoveredRefill_ancestry M N zL zH tag c (fun i => (x i).1) (fun i => (hx i).1) b)]
  exact source_retained_population_with_service zL zH hzL hzH hsL hsH M N J hJ hN hlarge
    tag q hq hclock hk c (fun i => (hv i).2) he

end SerialTransferSelection
