import proofs.ProductiveMemory.ExtractionBatchService
import proofs.SerialTransferSelection.CycleTransferInputs
import proofs.SerialTransferSelection.TransferJointProbability

namespace ProductiveMemory
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem productive_good_transfer_inputs (N M J : ℕ) (hN : 0 < N) (hM : 0 < M)
    (rho zL zH : ℝ) (s : ProductiveState) (hs : ProductiveReadyPopulation N M rho zL zH s)
    (p : ℝ) (hp : ∀ tag, p*(M : ℝ) ≤ ancestralCount tag s.population.live)
    {D : Finset ProductiveState} (x : ProductiveStopped D)
    (hx : x ∈ productiveBatchGoodSet N (membrane s.population.live) J
      (ancestralMembrane true s.population.live) (ancestralMembrane false s.population.live) rho zL zH D) :
    let t := (productivePhysical N x).population
    2 ≤ t.live.length ∧ M ≤ t.live.length ∧ t.live.length ≤ 8*M ∧
      ValidVolumes N t ∧ (∀ tag, (N : ℝ)*p*M ≤ ancestralMembrane tag t.live) ∧
      ∀ c ∈ t.live, extractionCellEnergy rho zL zH c < 8*readyLevel := by
  obtain ⟨e,rfl,_,hv,he,hw,hH,hL,_⟩ := hx
  dsimp only [productivePhysical]
  obtain ⟨hlen,_,_,hvs,_,_⟩ := hs
  obtain ⟨hl,hm,hcap⟩ := SerialTransferSelection.phase_endpoint_cell_bounds N M hN hM s.population (productiveOutcome N e.1.val e.2).population
    hlen hvs hv hw
  refine ⟨hl,hm,hcap,hv,?_,he⟩
  intro tag
  have hi := SerialTransferSelection.ready_ancestral_membrane_floor N M s.population hvs p tag (hp tag)
  have ha : ancestralMembrane tag s.population.live ≤ ancestralMembrane tag (productiveOutcome N e.1.val e.2).population.live := by
    cases tag
    · exact hL
    · exact hH
  exact hi.trans (by exact_mod_cast ha)


theorem productive_neutral_transfer_probability (N M J : ℕ) (hN : 0 < N) (hM : 0 < M)
    (rho zL zH : ℝ) (s : ProductiveState) (hs : ProductiveReadyPopulation N M rho zL zH s)
    (p eps : ℝ) (hp : 0 < p) (heps : 0 < eps)
    (hfloor : ∀ tag, p*(M:ℝ) ≤ ancestralCount tag s.population.live)
    {D : Finset ProductiveState} (x : ProductiveStopped D)
    (hx : x ∈ productiveBatchGoodSet N (membrane s.population.live) J
      (ancestralMembrane true s.population.live) (ancestralMembrane false s.population.live) rho zL zH D) :
    ∃ hM : M ≤ (productivePhysical N x).population.live.length,
      1-32/(eps^2*p*(M:ℝ)) ≤
        (SerialTransferSelection.uniformTransferLaw (productivePhysical N x).population.live.length M hM).expect
          (FiniteKernel.eventIndicator (SerialTransferSelection.ancestralTransferGoodSet N M
            (productivePhysical N x).population hM eps)) := by
  have hg := productive_good_transfer_inputs N M J hN hM rho zL zH s hs p hfloor x hx
  exact ⟨hg.2.1,SerialTransferSelection.source_transfer_weighted_probability N M hN hM _ hg.1 hg.2.1
    hg.2.2.1 hg.2.2.2.1 p eps hp heps hg.2.2.2.2.1⟩

end ProductiveMemory
