import proofs.SerialTransferSelection.RecoveryRestart

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

variable (N M J : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
  (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
  (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
  (s : PopulationState) (hv : ValidVolumes N s)
  (he : ∀ c ∈ s.live, cellEnergy zL zH c < 8*innerEnergy)
  (q : NNReal) (hq : 0 < (q : ℝ))
  (hclock : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ q)

noncomputable def selectedRecoveryLaw (S : TransferSubset s.live.length M) :
    FiniteLaw (Option (ReadyPopulation N M zL zH)) :=
  recoveryRestartLaw M N J hN zL zH hzL hzH (fun i => (retainedVector M s S i).high)
    (retainedRecoveryInput N M hN zL zH hzL hzH s hv he S)
    (fun i => hv _ (retainedVector_mem M s S i)) q hq (fun _i x => hclock _ x)

def selectedAncestryPreserved (S : TransferSubset s.live.length M)
    (y : ReadyPopulation N M zL zH) : Prop :=
  ∀ b, ancestralCount b y.val.live=ancestralCount b (exchangeSelectedMedium M s S).live ∧
    ancestralMembrane b y.val.live=ancestralMembrane b (exchangeSelectedMedium M s S).live

theorem selectedRecoveryLaw_probability
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (hJ : 0 < J)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (S : TransferSubset s.live.length M) :
    1-(M : ℝ)*(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*(q : ℝ)/J) ≤
      (selectedRecoveryLaw N M J hN zL zH hzL hzH s hv he q hq hclock S).expect
        (FiniteKernel.eventIndicator (successfulOutput (selectedAncestryPreserved N M zL zH s S))) := by
  have hr := recoveryRestartLaw_probability M N J hN zL zH hzL hzH
    (fun i => (retainedVector M s S i).high)
    (retainedRecoveryInput N M hN zL zH hzL hzH s hv he S)
    (fun i => hv _ (retainedVector_mem M s S i)) hsL hsH hlarge hJ q hq
    (fun i x => hclock _ x) hk (by
      intro j
      change recoveryEnergy (retainedVector M s S j).high
        (fun i => concentration (retainedVector M s S j).compartment.2
          (retainedVector M s S j).compartment.1 i-
          recoveryCenter zL zH (retainedVector M s S j).high i) ≤ _
      rw [tagged_recovery_energy]
      exact (he _ (retainedVector_mem M s S j)).le)
  have hlist : List.ofFn (fun i => (⟨(retainedVector M s S i).high,
      (retainedRecoveryInput N M hN zL zH hzL hzH s hv he S i).val⟩ : TaggedCell)) =
      (exchangeSelectedMedium M s S).live := by
    convert retainedVector_list M s S using 1
  have hrel : recoveryPreservesAncestry M N zL zH
      (fun i => (retainedVector M s S i).high)
      (retainedRecoveryInput N M hN zL zH hzL hzH s hv he S) =
      selectedAncestryPreserved N M zL zH s S := by
    funext y
    simp only [recoveryPreservesAncestry,selectedAncestryPreserved,hlist]
  rw [hrel] at hr
  exact hr

end SerialTransferSelection
