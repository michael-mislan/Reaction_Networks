import proofs.SerialTransferSelection.BatchJointProbability
import proofs.SerialTransferSelection.TransferJointProbability

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem phase_endpoint_cell_bounds (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (s t : PopulationState) (hs : s.live.length=M) (hvs : ValidVolumes N s)
    (hvt : ValidVolumes N t) (hw : membrane t.live=4*membrane s.live) :
    2 ≤ t.live.length ∧ M ≤ t.live.length ∧ t.live.length ≤ 8*M := by
  have hslo := membrane_lower N s.live (fun c hc => (hvs c hc).1)
  have hshi := membrane_upper N s.live (fun c hc => (hvs c hc).2.le)
  have htlo := membrane_lower N t.live (fun c hc => (hvt c hc).1)
  have hthi := membrane_upper N t.live (fun c hc => (hvt c hc).2.le)
  rw [hs] at hslo hshi
  have hlo : N*(2*M) ≤ N*t.live.length := by nlinarith only [hslo,hthi,hw]
  have hhi : N*t.live.length ≤ N*(8*M) := by nlinarith only [hshi,htlo,hw]
  have hlow : 2*M ≤ t.live.length := by nlinarith only [hlo,hN]
  have hupp : t.live.length ≤ 8*M := by nlinarith only [hhi,hN]
  omega

theorem ready_ancestral_membrane_floor (N M : ℕ) (s : PopulationState)
    (hv : ValidVolumes N s) (p : ℝ) (tag : Bool)
    (hp : p*(M : ℝ) ≤ ancestralCount tag s.live) :
    (N : ℝ)*p*M ≤ ancestralMembrane tag s.live := by
  have hn := (ancestral_count_bounds N tag s.live (fun c hc =>
    ⟨(hv c hc).1,(hv c hc).2.le⟩)).1
  have hr : (N : ℝ)*ancestralCount tag s.live ≤ ancestralMembrane tag s.live := by
    exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith only [hr,hm]

/-- The proved batch endpoint supplies every geometric and ancestry hypothesis
of intact uniform transfer. These are consequences, not fresh kernel assumptions. -/
theorem phase_good_transfer_inputs (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (zL zH : ℝ) (s : PopulationState) (hs : PhaseReadyPopulation N M zL zH s)
    (p : ℝ) (hp : ∀ tag, p*(M : ℝ) ≤ ancestralCount tag s.live)
    {D : Finset PopulationState} (x : StoppedPopulation D)
    (hx : x ∈ phaseBatchGoodSet N (membrane s.live)
      (ancestralMembrane true s.live) (ancestralMembrane false s.live) zL zH D) :
    let t := physicalState N x
    2 ≤ t.live.length ∧ M ≤ t.live.length ∧ t.live.length ≤ 8*M ∧
      ValidVolumes N t ∧ (∀ tag, (N : ℝ)*p*M ≤ ancestralMembrane tag t.live) ∧
      ∀ c ∈ t.live, cellEnergy zL zH c < 8*innerEnergy := by
  obtain ⟨e,rfl,_,hv,he,hw,hH,hL,_⟩ := hx
  dsimp only [physicalState]
  obtain ⟨hlen,_,_,hvs,_⟩ := hs
  obtain ⟨hl,hm,hcap⟩ := phase_endpoint_cell_bounds N M hN hM s (eventOutcome N e)
    hlen hvs hv hw
  refine ⟨hl,hm,hcap,hv,?_,he⟩
  intro tag
  have hi := ready_ancestral_membrane_floor N M s hvs p tag (hp tag)
  have ha : ancestralMembrane tag s.live ≤ ancestralMembrane tag (eventOutcome N e).live := by
    cases tag
    · exact hL
    · exact hH
  exact hi.trans (by exact_mod_cast ha)

end SerialTransferSelection
