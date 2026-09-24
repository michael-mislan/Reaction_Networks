import proofs.FiniteCopyReactor.PulseMaterial

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding Classical
open scoped BigOperators

def pulseProbability (N : Counts) (p : Intervention) (E : Set (PulseOutcome N)) : ℝ :=
  ∑ o, if o ∈ E then pulseMass N p o else 0

theorem pulseProbability_mono (N : Counts) (p : Intervention) {E F : Set (PulseOutcome N)}
    (h : E ⊆ F) : pulseProbability N p E ≤ pulseProbability N p F := by
  classical
  unfold pulseProbability
  apply Finset.sum_le_sum
  intro o _
  by_cases he : o ∈ E
  · simp only [if_pos he,if_pos (h he),le_refl]
  · simp only [if_neg he]
    split_ifs
    · exact pulseMass_nonneg N p o
    · exact le_rfl

theorem pulseProbability_union (N : Counts) (p : Intervention) (E F : Set (PulseOutcome N)) :
    pulseProbability N p (E ∪ F) ≤ pulseProbability N p E+pulseProbability N p F := by
  classical
  unfold pulseProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro o _
  have h := pulseMass_nonneg N p o
  by_cases he : o ∈ E <;> by_cases hf : o ∈ F <;> simp [he,hf]
  linarith

theorem pulse_material_low_tail (side : Bool) (N : Counts) (V : ℕ) (p : Intervention)
    (hV : 1000 ≤ V) (hl : (159/160)*(V:ℝ) ≤ unitObs side N)
    (hu : unitObs side N ≤ (161/160)*(V:ℝ)) :
    pulseProbability N p {o | unitObs side (postPulseCounts N V p o) < (24/25)*(V:ℝ)} ≤
      Real.exp (-(V:ℝ)/100000) := by
  have hcenter := (pulse_material_center side N V p hl hu).1
  have hv : (1000:ℝ) ≤ V := by exact_mod_cast hV
  have h := pulse_deviation_tail N p (fun m => materialWeight side m.1) V (-1)
    (fun m => (materialWeight_bounds side m.1).1)
    (fun m => (materialWeight_bounds side m.1).2) (by norm_num)
    (by rw [material_weight_total]; exact hu)
  apply le_trans _ h
  unfold pulseProbability deviationTail
  apply Finset.sum_le_sum
  intro o _
  by_cases he : unitObs side (postPulseCounts N V p o) < (24/25)*(V:ℝ)
  · have hh : (V:ℝ)/100 ≤ -1*(retainedStock N (fun m => materialWeight side m.1) o-
        retainedMean N p (fun m => materialWeight side m.1)) := by
      rw [postPulse_material_eq] at he
      linarith
    simp only [Set.mem_setOf_eq,if_pos he,if_pos hh,le_refl]
  · simp only [Set.mem_setOf_eq,if_neg he]
    split_ifs
    · exact pulseMass_nonneg N p o
    · exact le_rfl

theorem pulse_material_high_tail (side : Bool) (N : Counts) (V : ℕ) (p : Intervention)
    (hl : (159/160)*(V:ℝ) ≤ unitObs side N)
    (hu : unitObs side N ≤ (161/160)*(V:ℝ)) :
    pulseProbability N p {o | (51/50)*(V:ℝ) < unitObs side (postPulseCounts N V p o)} ≤
      Real.exp (-(V:ℝ)/100000) := by
  have hcenter := (pulse_material_center side N V p hl hu).2
  have h := pulse_deviation_tail N p (fun m => materialWeight side m.1) V 1
    (fun m => (materialWeight_bounds side m.1).1)
    (fun m => (materialWeight_bounds side m.1).2) (by norm_num)
    (by rw [material_weight_total]; exact hu)
  apply le_trans _ h
  unfold pulseProbability deviationTail
  apply Finset.sum_le_sum
  intro o _
  by_cases he : (51/50)*(V:ℝ) < unitObs side (postPulseCounts N V p o)
  · have hh : (V:ℝ)/100 ≤ 1*(retainedStock N (fun m => materialWeight side m.1) o-
        retainedMean N p (fun m => materialWeight side m.1)) := by
      rw [postPulse_material_eq] at he
      linarith [Nat.cast_nonneg (α := ℝ) V]
    simp only [Set.mem_setOf_eq,if_pos he,if_pos hh,le_refl]
  · simp only [Set.mem_setOf_eq,if_neg he]
    split_ifs
    · exact pulseMass_nonneg N p o
    · exact le_rfl

def BadPulseMaterial (N : Counts) (V : ℕ) (p : Intervention) : Set (PulseOutcome N) :=
  {o | ∃ side : Bool, unitObs side (postPulseCounts N V p o) < (24/25)*(V:ℝ) ∨
    (51/50)*(V:ℝ) < unitObs side (postPulseCounts N V p o)}

theorem pulse_material_probability (N : Counts) (V : ℕ) (p : Intervention)
    (hV : 1000 ≤ V) (hN : Restart V N) :
    pulseProbability N p (BadPulseMaterial N V p) ≤ 4*Real.exp (-(V:ℝ)/100000) := by
  have hb (side : Bool) : (159/160)*(V:ℝ) ≤ unitObs side N ∧ unitObs side N ≤ (161/160)*(V:ℝ) := by
    cases side
    · change _ ≤ wCount N ∧ wCount N ≤ _
      constructor <;> linarith [hN.2.2.1,hN.2.2.2.1]
    · change _ ≤ uCount N ∧ uCount N ≤ _
      constructor <;> linarith [hN.1,hN.2.1]
  let E (side : Bool) : Set (PulseOutcome N) :=
    {o | unitObs side (postPulseCounts N V p o) < (24/25)*(V:ℝ)} ∪
    {o | (51/50)*(V:ℝ) < unitObs side (postPulseCounts N V p o)}
  have he (side : Bool) : pulseProbability N p (E side) ≤ 2*Real.exp (-(V:ℝ)/100000) := by
    have hu := pulseProbability_union N p
      {o | unitObs side (postPulseCounts N V p o) < (24/25)*(V:ℝ)}
      {o | (51/50)*(V:ℝ) < unitObs side (postPulseCounts N V p o)}
    have hl := pulse_material_low_tail side N V p hV (hb side).1 (hb side).2
    have hh := pulse_material_high_tail side N V p (hb side).1 (hb side).2
    dsimp [E]
    linarith
  have heq : BadPulseMaterial N V p = E false ∪ E true := by
    ext o
    simp [BadPulseMaterial,E,Bool.exists_bool]
  rw [heq]
  have h := pulseProbability_union N p (E false) (E true)
  linarith [he false,he true]

end
end FiniteCopyReactor
