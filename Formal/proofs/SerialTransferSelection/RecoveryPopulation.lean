import proofs.SerialTransferSelection.RecoveryEndpoint
import proofs.SerialTransferSelection.RecoveryProduct

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

noncomputable def recoveryCenter (zL zH : ℝ) (tag : Bool) : Point :=
  pointOfState (lift sourceRates (if tag then zH else zL))

noncomputable def recoveryEnergy (tag : Bool) : Point → ℝ :=
  if tag then highEnergy else lowEnergy

noncomputable def recoveryCellDomain (N : ℕ) (zL zH : ℝ) (tag : Bool) : Finset Compartment :=
  growthDomain N (recoveryCenter zL zH tag) (recoveryEnergy tag) outerEnergy

noncomputable def recoveryCellModel (N : ℕ) (zL zH : ℝ) (tag : Bool) :=
  stoppedGrowthModel 0 (by norm_num) N (recoveryCellDomain N zL zH tag)

theorem source_tagged_endpoint_return (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N) (tag : Bool)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (recoveryCellModel N zL zH tag).total x ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (c : {c : Compartment // c ∈ recoveryCellDomain N zL zH tag})
    (hc : c.val.2 < 2*N)
    (he : recoveryEnergy tag (fun i => concentration c.val.2 c.val.1 i-recoveryCenter zL zH tag i) ≤ 8*innerEnergy) :
    1-recoveryError ((N : ℝ)*localAlpha*innerEnergy) ≤
      ((recoveryCellModel N zL zH tag).uniformize q hq hclock).poissonized (q*5376)
        (FiniteKernel.eventIndicator (readyRecoverySet N c.val.2 (recoveryCenter zL zH tag) (recoveryEnergy tag))) (some c) := by
  cases tag with
  | false => exact low_endpoint_return zL hzL hsL N hN hlarge q hq hclock hk c hc he
  | true => exact high_endpoint_return zH hzH hsH N hN hlarge q hq hclock hk c hc he

/-- Literal resident recovery, separately clocked for each actual retained cell.
The domain and the zero-precursor source are fixed before the outcome is drawn. -/
noncomputable def retainedPopulationRecoveryLaw (M N : ℕ) (zL zH : ℝ)
    (tag : Fin M → Bool) (q : Fin M → NNReal) (hq : ∀ i, 0 < (q i : ℝ))
    (hclock : ∀ i x, (recoveryCellModel N zL zH (tag i)).total x ≤ q i)
    (c : ∀ i, {c : Compartment // c ∈ recoveryCellDomain N zL zH (tag i)}) :
    FiniteLaw (∀ i, StoppedCompartment (recoveryCellDomain N zL zH (tag i))) :=
  recoveryProductLaw (fun i => poissonLaw
    ((recoveryCellModel N zL zH (tag i)).uniformize (q i) (hq i) (hclock i))
    (q i*5376) (some (c i)))

/-- Uniform return of all actual retained states; every coordinate failure is retained.
This conditional statement allows arbitrary phases and correlated transfer history. -/
theorem source_retained_population_return (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (M N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (tag : Fin M → Bool) (q : Fin M → NNReal) (hq : ∀ i, 0 < (q i : ℝ))
    (hclock : ∀ i x, (recoveryCellModel N zL zH (tag i)).total x ≤ q i)
    (hk : ∀ i, (N : ℝ)*localAlpha*innerEnergy/672 ≤ q i)
    (c : ∀ i, {c : Compartment // c ∈ recoveryCellDomain N zL zH (tag i)})
    (hc : ∀ i, (c i).val.2 < 2*N)
    (he : ∀ j, recoveryEnergy (tag j) (fun i => concentration (c j).val.2 (c j).val.1 i-
      recoveryCenter zL zH (tag j) i) ≤ 8*innerEnergy) :
    1-(M : ℝ)*recoveryError ((N : ℝ)*localAlpha*innerEnergy) ≤
      (retainedPopulationRecoveryLaw M N zL zH tag q hq hclock c).expect
        (FiniteKernel.eventIndicator {x | ∀ i,
          x i ∈ readyRecoverySet N (c i).val.2 (recoveryCenter zL zH (tag i)) (recoveryEnergy (tag i))}) := by
  have h := recoveryProductLaw_lower
    (fun i => poissonLaw ((recoveryCellModel N zL zH (tag i)).uniformize (q i) (hq i) (hclock i))
      (q i*5376) (some (c i)))
    (fun i => readyRecoverySet N (c i).val.2 (recoveryCenter zL zH (tag i)) (recoveryEnergy (tag i)))
    (recoveryError ((N : ℝ)*localAlpha*innerEnergy))
    (by unfold recoveryError localAlpha innerEnergy outerEnergy; positivity)
    (by
      intro i
      rw [poissonLaw_expect]
      exact source_tagged_endpoint_return zL zH hzL hzH hsL hsH N hN hlarge (tag i)
        (q i) (hq i) (hclock i) (hk i) (c i) (hc i) (he i))
  simpa only [Fintype.card_fin] using h

end SerialTransferSelection
