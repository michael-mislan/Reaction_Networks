import proofs.SerialTransferSelection.RecoveryPopulation
import proofs.SerialTransferSelection.ServiceJoint

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem source_tagged_return_with_service (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (N J : ℕ) (hJ : 0 < J) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N) (tag : Bool)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (recoveryCellModel N zL zH tag).total x ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (c : {c : Compartment // c ∈ recoveryCellDomain N zL zH tag})
    (hc : c.val.2 < 2*N)
    (he : recoveryEnergy tag (fun i => concentration c.val.2 c.val.1 i-recoveryCenter zL zH tag i) ≤ 8*innerEnergy) :
    1-(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*(q : ℝ)/J) ≤
      ((serviceCounterModel (recoveryCellModel N zL zH tag) J).uniformize q hq (fun x => hclock x.1)).poissonized (q*5376)
        (FiniteKernel.eventIndicator {x | x.1 ∈ readyRecoverySet N c.val.2 (recoveryCenter zL zH tag) (recoveryEnergy tag) ∧ x.2.val < J}) (some c, 0) := by
  have hs := source_tagged_endpoint_return zL zH hzL hzH hsL hsH N hN hlarge tag q hq hclock hk c hc he
  have hj := service_joint_lower (recoveryCellModel N zL zH tag) J hJ q 5376 hq hclock
    (readyRecoverySet N c.val.2 (recoveryCenter zL zH tag) (recoveryEnergy tag)) (some c)
  norm_num only [NNReal.coe_ofNat] at hj
  apply le_trans _ hj
  linarith only [hs]

noncomputable def retainedPopulationServiceLaw (M N J : ℕ) (zL zH : ℝ)
    (tag : Fin M → Bool) (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ i x, (recoveryCellModel N zL zH (tag i)).total x ≤ q)
    (c : ∀ i, {c : Compartment // c ∈ recoveryCellDomain N zL zH (tag i)}) :
    FiniteLaw (∀ i, (StoppedCompartment (recoveryCellDomain N zL zH (tag i)) × Fin (J+1))) :=
  recoveryProductLaw (fun i => poissonLaw
    ((serviceCounterModel (recoveryCellModel N zL zH (tag i)) J).uniformize q hq (fun x => hclock i x.1))
    (q*5376) (some (c i), 0))

/-- Uniform return of all actual retained states; every coordinate failure is retained.
This conditional statement allows arbitrary phases and correlated transfer history. -/
theorem source_retained_population_with_service (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (M N J : ℕ) (hJ : 0 < J) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (tag : Fin M → Bool) (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ i x, (recoveryCellModel N zL zH (tag i)).total x ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (c : ∀ i, {c : Compartment // c ∈ recoveryCellDomain N zL zH (tag i)})
    (hc : ∀ i, (c i).val.2 < 2*N)
    (he : ∀ j, recoveryEnergy (tag j) (fun i => concentration (c j).val.2 (c j).val.1 i-
      recoveryCenter zL zH (tag j) i) ≤ 8*innerEnergy) :
    1-(M : ℝ)*(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*(q : ℝ)/J) ≤
      (retainedPopulationServiceLaw M N J zL zH tag q hq hclock c).expect
        (FiniteKernel.eventIndicator {x | ∀ i,
          (x i).1 ∈ readyRecoverySet N (c i).val.2 (recoveryCenter zL zH (tag i)) (recoveryEnergy (tag i)) ∧ (x i).2.val < J}) := by
  have h := recoveryProductLaw_lower
    (fun i => poissonLaw ((serviceCounterModel (recoveryCellModel N zL zH (tag i)) J).uniformize q hq (fun x => hclock i x.1))
      (q*5376) (some (c i), 0))
    (fun i => {x | x.1 ∈ readyRecoverySet N (c i).val.2 (recoveryCenter zL zH (tag i)) (recoveryEnergy (tag i)) ∧ x.2.val < J})
    ((recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*(q : ℝ)/J))
    (by unfold recoveryError localAlpha innerEnergy outerEnergy; positivity)
    (by
      intro i
      rw [poissonLaw_expect]
      exact source_tagged_return_with_service zL zH hzL hzH hsL hsH N J hJ hN hlarge (tag i)
        q hq (hclock i) hk (c i) (hc i) (he i))
  simpa only [Fintype.card_fin] using h


end SerialTransferSelection
