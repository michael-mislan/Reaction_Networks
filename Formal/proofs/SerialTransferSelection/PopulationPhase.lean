import proofs.SerialTransferSelection.CycleOutcome
import proofs.SerialTransferSelection.PhaseCorrection

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

noncomputable def countLogOdds (s : PopulationState) : ℝ :=
  Real.log (ancestralCount true s.live)-Real.log (ancestralCount false s.live)

noncomputable def populationPhase (s : PopulationState) : ℝ :=
  Real.log (((ancestralMembrane true s.live : ℝ)/(ancestralCount true s.live : ℝ))/
    ((ancestralMembrane false s.live : ℝ)/(ancestralCount false s.live : ℝ)))

theorem population_phase_identity_bounds (N : ℕ) (hN : 0 < N) (s : PopulationState)
    (hv : ValidVolumes N s) (hc : ∀ b, 0 < ancestralCount b s.live) :
    countLogOdds s=sizeLogOdds s-populationPhase s ∧
      -Real.log 2 ≤ populationPhase s ∧ populationPhase s ≤ Real.log 2 := by
  have hcr (b : Bool) : (0 : ℝ) < ancestralCount b s.live := by exact_mod_cast hc b
  have hb (b : Bool) := ancestral_count_bounds N b s.live (fun c hc =>
    ⟨(hv c hc).1,(hv c hc).2.le⟩)
  have hbr (b : Bool) : (N : ℝ)*ancestralCount b s.live ≤ ancestralMembrane b s.live ∧
      (ancestralMembrane b s.live : ℝ) ≤ 2*(N : ℝ)*ancestralCount b s.live := by
    exact_mod_cast hb b
  have hbp (b : Bool) : (0 : ℝ) < ancestralMembrane b s.live :=
    (mul_pos (by exact_mod_cast hN) (hcr b)).trans_le (hbr b).1
  have hmean (b : Bool) : (N : ℝ) ≤ (ancestralMembrane b s.live : ℝ)/ancestralCount b s.live ∧
      (ancestralMembrane b s.live : ℝ)/ancestralCount b s.live ≤ 2*(N : ℝ) := by
    exact ⟨(le_div_iff₀ (hcr b)).mpr (hbr b).1,(div_le_iff₀ (hcr b)).mpr (hbr b).2⟩
  constructor
  · have hi := count_size_phase_identity (ancestralMembrane true s.live) (ancestralMembrane false s.live)
      (ancestralCount true s.live) (ancestralCount false s.live) (hbp true) (hbp false) (hcr true) (hcr false)
    rw [Real.log_div (ne_of_gt (hcr true)) (ne_of_gt (hcr false)),
      Real.log_div (ne_of_gt (hbp true)) (ne_of_gt (hbp false))] at hi
    exact hi
  · exact mean_size_phase_bounds N _ _ (by exact_mod_cast hN)
      (hmean true).1 (hmean true).2 (hmean false).1 (hmean false).2

/-- No intermediate phase penalty is charged. Both endpoints are actual retained
populations, and the gain is in cell counts. -/
theorem endpoint_count_gain (N : ℕ) (hN : 0 < N) (s t : PopulationState)
    (hvs : ValidVolumes N s) (hvt : ValidVolumes N t)
    (hcs : ∀ b, 0 < ancestralCount b s.live) (hct : ∀ b, 0 < ancestralCount b t.live)
    (g : ℝ) (hg : g < sizeLogOdds t-sizeLogOdds s) :
    g-2*Real.log 2 < countLogOdds t-countLogOdds s := by
  have hs := population_phase_identity_bounds N hN s hvs hcs
  have ht := population_phase_identity_bounds N hN t hvt hct
  rw [hs.1,ht.1]
  linarith only [hg,hs.2.1,ht.2.2]

end SerialTransferSelection
