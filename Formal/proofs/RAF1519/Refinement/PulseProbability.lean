import proofs.RAF1519.Refinement.PulseBadUnion
import proofs.RAF1519.Refinement.CategoricalMeasure

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option maxHeartbeats 40000

theorem graphPulsePMF_event {n : ℕ} (N : MolecularState n) (p : Fin n → Intervention)
    (E : Set (PulseOutcomes N)) :
    (graphPulsePMF N p).toMeasure E = ENNReal.ofReal (categoricalProbability (graphPulseCategory N p) E) :=
  categoricalPMF_event (graphPulseCategory N p) (graphPulseCategory_nonnegative N p)
    (graphPulseCategory_total N p) E

theorem graphPulse_preparation_failure {n : ℕ} (N : MolecularState n) (V : ℕ) (hV : 10000 ≤ V)
    (p : Fin n → Intervention) (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s)))) :
    (graphPulsePMF N p).toMeasure {o | ¬CountPrepared V (postPulseState N V p o)} ≤
      ENNReal.ofReal (4*n*Real.exp (-(V:ℝ)/100000)+n*Real.exp (-(V:ℝ)/100000000)) := by
  have hV0 : (0:ℝ) < V := by exact_mod_cast (show 0 < V by omega)
  apply le_trans (measure_mono ?_)
    ((graphPulsePMF_event N p (pulseBad N V p)).trans_le (ENNReal.ofReal_le_ofReal
      (pulseBad_probability N V hV0 p hready)))
  intro o ho
  by_contra hb
  exact ho (postPulse_prepared_of_not_bad N V hV p hready o hb)

end
end RAF1519.Refinement
