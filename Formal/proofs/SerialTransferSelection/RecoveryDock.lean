import proofs.SerialTransferSelection.RecoveryService
import proofs.SerialTransferSelection.TransferPhysical

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem tagged_recovery_energy (zL zH : ℝ) (c : TaggedCell) :
    recoveryEnergy c.high (fun i => concentration c.compartment.2 c.compartment.1 i-
      recoveryCenter zL zH c.high i) = cellEnergy zL zH c := by
  cases hc : c.high <;> simp [recoveryEnergy,recoveryCenter,cellEnergy,hc]

theorem tagged_recovery_domain (N : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (c : TaggedCell) (hv : N ≤ c.compartment.2 ∧ c.compartment.2 < 2*N)
    (he : cellEnergy zL zH c < 8*innerEnergy) :
    c.compartment ∈ recoveryCellDomain N zL zH c.high := by
  have he' : recoveryEnergy c.high (fun i => concentration c.compartment.2 c.compartment.1 i-
      recoveryCenter zL zH c.high i) < outerEnergy := by
    rw [tagged_recovery_energy]
    exact he.trans (by norm_num [innerEnergy,outerEnergy])
  cases ht : c.high
  · apply (mem_growthDomain N hN c.compartment _ (lowroot_upper zL hzL)
      lowEnergy lowEnergy_lower outerEnergy (by norm_num [outerEnergy])).mpr
    exact ⟨hv.1,hv.2.le,by simpa [ht,recoveryEnergy,recoveryCenter] using he'⟩
  · apply (mem_growthDomain N hN c.compartment _ (highroot_upper zH hzH)
      highEnergy highEnergy_lower outerEnergy (by norm_num [outerEnergy])).mpr
    exact ⟨hv.1,hv.2.le,by simpa [ht,recoveryEnergy,recoveryCenter] using he'⟩

def retainedVector (M : ℕ) (s : PopulationState) (S : TransferSubset s.live.length M)
    (i : Fin M) : TaggedCell :=
  selectedCell (exchangeSelectedMedium M s S)
    ⟨i.val, by rw [exchangeSelectedMedium_length]; exact i.isLt⟩

theorem retainedVector_mem (M : ℕ) (s : PopulationState) (S : TransferSubset s.live.length M)
    (i : Fin M) : retainedVector M s S i ∈ s.live :=
  exchangeSelectedMedium_preserves M s S _ (selected_mem _ _)

theorem retainedVector_list (M : ℕ) (s : PopulationState) (S : TransferSubset s.live.length M) :
    List.ofFn (retainedVector M s S) = (exchangeSelectedMedium M s S).live := by
  apply List.ext_getElem
  · simp [exchangeSelectedMedium_length]
  · intro i hi hj
    simp [retainedVector,selectedCell]

/-- These are the literal selected compartments, admitted to recovery by the
batch safe endpoint rather than by a new return assumption. -/
noncomputable def retainedRecoveryInput (N M : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : PopulationState) (hv : ValidVolumes N s)
    (he : ∀ c ∈ s.live, cellEnergy zL zH c < 8*innerEnergy)
    (S : TransferSubset s.live.length M) (i : Fin M) :
    {c : Compartment // c ∈ recoveryCellDomain N zL zH (retainedVector M s S i).high} :=
  ⟨(retainedVector M s S i).compartment,
    tagged_recovery_domain N hN zL zH hzL hzH _ (hv _ (retainedVector_mem M s S i))
      (he _ (retainedVector_mem M s S i))⟩

end SerialTransferSelection
