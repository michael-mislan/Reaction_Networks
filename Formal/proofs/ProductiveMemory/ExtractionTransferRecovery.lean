import proofs.ProductiveMemory.ExtractionSelectedRecovery
import proofs.SerialTransferSelection.TransferRecovery

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

def extractionTransferRelation (N M : ℕ) (rho zL zH : ℝ) (s : PopulationState) (p eps : ℝ)
    (y : ProductiveReady N M rho zL zH) : Prop :=
  (∀ b, 0 < ancestralCount b y.val.population.live ∧
    (1-eps)*p/16 ≤ (ancestralCount b y.val.population.live:ℝ)/(M:ℝ)) ∧
  Real.log (ancestralMembrane true s.live)-Real.log (ancestralMembrane false s.live)-Real.log ((1+eps)/(1-eps)) ≤
    Real.log (ancestralMembrane true y.val.population.live)-Real.log (ancestralMembrane false y.val.population.live)

theorem extraction_transfer_preserved_relation (N M : ℕ) (hN : 0 < N) (hMpos : 0 < M)
    (rho zL zH : ℝ) (s : PopulationState) (hM : M ≤ s.live.length)
    (hcap : s.live.length ≤ 8*M) (hv : ValidVolumes N s)
    (p eps : ℝ) (hp : 0 < p) (heps : 0 < eps) (heps1 : eps < 1)
    (hB : ∀ b, (N:ℝ)*p*M ≤ ancestralMembrane b s.live)
    (S : SerialTransferSelection.TransferSubset s.live.length M)
    (hg : S ∈ SerialTransferSelection.ancestralTransferGoodSet N M s hM eps)
    (y : ProductiveReady N M rho zL zH) (hy : extractionSelectedAncestry N M rho zL zH s S y) :
    extractionTransferRelation N M rho zL zH s p eps y := by
  have hpres := extraction_selected_ancestry_physical N M rho zL zH s S y hy
  constructor
  · intro b
    rw [(hpres b).1]
    exact SerialTransferSelection.transfer_count_frequency_floor N M hN hMpos b s (by omega) hM hcap hv p eps hp
      heps.le heps1 (hB b) S (hg b)
  · rw [(hpres true).2,(hpres false).2]
    have hpos (b : Bool) : 0 < ancestralMembrane b s.live := by
      have h := (by positivity : (0:ℝ) < (N:ℝ)*p*M).trans_le (hB b)
      exact_mod_cast h
    exact SerialTransferSelection.transfer_size_odds_loss N M hN hMpos s (by omega) hM eps heps.le heps1
      (hpos true) (hpos false) S hg

variable (N M : ℕ) (hN : 1 ≤ N) (hlarge : recoveryCount ≤ N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : PopulationState) (hM : M ≤ s.live.length) (hv : ValidVolumes N s)
    (he : ∀ c ∈ s.live, extractionCellEnergy rho zL zH c < 8*readyLevel)

/-- Uniform intact sampling never inspects ancestry success before continuing recovery. -/
def extractionTransferRecoveryLaw : FiniteLaw (Option (ProductiveReady N M rho zL zH)) :=
  (SerialTransferSelection.uniformTransferLaw s.live.length M hM).bind
    (extractionSelectedRecoveryLaw N M hN hlarge rho zL zH hr hzL hzH s hv he)

theorem extraction_transfer_recovery_probability
    (heL : extractDrift rho 0 (lift rho zL)=0) (heH : extractDrift rho 0 (lift rho zH)=0)
    (hMpos : 0 < M) (hL : 2 ≤ s.live.length) (hcap : s.live.length ≤ 8*M)
    (p eps : ℝ) (hp : 0 < p) (heps : 0 < eps) (heps1 : eps < 1)
    (hB : ∀ b, (N:ℝ)*p*M ≤ ancestralMembrane b s.live) :
    1-(32/(eps^2*p*(M:ℝ))+2*(M:ℝ)/10^18) ≤
      (extractionTransferRecoveryLaw N M hN hlarge rho zL zH hr hzL hzH s hM hv he).expect
        (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput
          (extractionTransferRelation N M rho zL zH s p eps))) := by
  apply SerialTransferSelection.finiteLaw_joint_bind_lower _ _
    (SerialTransferSelection.ancestralTransferGoodSet N M s hM eps) _ _ _ (by positivity)
  · exact SerialTransferSelection.source_transfer_weighted_probability N M (by omega) hMpos s hL hM hcap hv p eps hp heps hB
  · intro S hS
    have hreturn := extraction_selected_probability N M hN hlarge rho zL zH hr hzL hzH s hv he S heL heH
    exact hreturn.trans (SerialTransferSelection.finiteLaw_successful_mono _ _ _ (fun y hy =>
      extraction_transfer_preserved_relation N M (by omega) hMpos rho zL zH s hM hcap hv p eps hp heps heps1 hB S hS y hy))

end
end ProductiveMemory
