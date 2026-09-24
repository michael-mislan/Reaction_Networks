import proofs.FiniteCopyReactor.PulseDeviation
import proofs.RandomViability.BindingUnitGenerator

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

def materialWeight (side : Bool) : Fin 6 → ℝ := if side then uUnits else wUnits
def materialDose (side : Bool) (V : ℕ) (p : Intervention) : ℕ := if side then doseU V p else doseW V p
def materialError (side : Bool) (p : Intervention) : ℝ := if side then p.eU else p.eW

theorem materialWeight_bounds (side : Bool) (i : Fin 6) :
    0 ≤ materialWeight side i ∧ materialWeight side i ≤ 2 := by
  cases side <;> fin_cases i <;> norm_num [materialWeight,uUnits,wUnits]

theorem material_weight_total (side : Bool) (N : Counts) :
    (∑ m : Molecules N, materialWeight side m.1) = unitObs side N := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  cases side <;> simp only [materialWeight,unitObs,Bool.false_eq_true,if_false,if_true,uCount,wCount]
  all_goals
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem material_retained_eq (side : Bool) (N : Counts) (o : PulseOutcome N) :
    retainedStock N (fun m => materialWeight side m.1) o = unitObs side (categoryCounts N o 0) := by
  have he (w : Fin 6 → ℝ) : retainedStock N (fun m => w m.1) o =
      ∑ i, w i*(categoryCounts N o 0 i:ℝ) := by
    unfold retainedStock
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    unfold categoryCounts
    rw [Nat.cast_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  cases side <;> exact he _

theorem postPulse_material_eq (side : Bool) (N : Counts) (V : ℕ)
    (p : Intervention) (o : PulseOutcome N) :
    unitObs side (postPulseCounts N V p o) =
      retainedStock N (fun m => materialWeight side m.1) o + materialDose side V p := by
  rw [material_retained_eq]
  cases side
  · simp only [unitObs,Bool.false_eq_true,if_false,materialDose]
    rw [wCount_expansion,wCount_expansion]
    norm_num [postPulseCounts]
    ring
  · simp only [unitObs,if_true,materialDose]
    rw [uCount_expansion,uCount_expansion]
    norm_num [postPulseCounts]
    ring

theorem material_dose_rounding (side : Bool) (V : ℕ) (p : Intervention) :
    (V:ℝ)*(1-p.q+materialError side p)-1 < (materialDose side V p:ℝ) ∧
    (materialDose side V p:ℝ) ≤ (V:ℝ)*(1-p.q+materialError side p) := by
  cases side
  · exact doseW_rounding V p
  · exact doseU_rounding V p

theorem material_error_bounds (side : Bool) (p : Intervention) :
    -(1/200) ≤ materialError side p ∧ materialError side p ≤ 1/200 := by
  cases side
  · exact ⟨p.eW_lower,p.eW_upper⟩
  · exact ⟨p.eU_lower,p.eU_upper⟩

/-- The actual transform center plus the literal integer dose has the promised margins. -/
theorem pulse_material_center (side : Bool) (N : Counts) (V : ℕ) (p : Intervention)
    (hl : (159/160)*(V:ℝ) ≤ unitObs side N)
    (hu : unitObs side N ≤ (161/160)*(V:ℝ)) :
    (31213/32000)*(V:ℝ)-1 ≤
      retainedMean N p (fun m => materialWeight side m.1)+materialDose side V p ∧
    retainedMean N p (fun m => materialWeight side m.1)+materialDose side V p ≤
      (3231/3200)*(V:ℝ) := by
  have hq : 0 ≤ p.q := by linarith [p.q_lower]
  have hmL : p.q*(49/50)*unitObs side N ≤ retainedMean N p (fun m => materialWeight side m.1) := by
    rw [← material_weight_total]
    unfold retainedMean
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (p.loss_lower m.1) hq)
      (materialWeight_bounds side m.1).1
  have hmU : retainedMean N p (fun m => materialWeight side m.1) ≤ p.q*unitObs side N := by
    rw [← material_weight_total]
    unfold retainedMean
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (p.loss_upper m.1) hq)
      (materialWeight_bounds side m.1).1
    simpa only [mul_one] using h
  have hlo := mul_le_mul_of_nonneg_left hl (show 0 ≤ p.q*(49/50) by positivity)
  have hhi := mul_le_mul_of_nonneg_left hu hq
  have hqv := mul_le_mul_of_nonneg_right p.q_upper (Nat.cast_nonneg (α := ℝ) V)
  have hel := mul_le_mul_of_nonneg_left (material_error_bounds side p).1 (Nat.cast_nonneg (α := ℝ) V)
  have heu := mul_le_mul_of_nonneg_left (material_error_bounds side p).2 (Nat.cast_nonneg (α := ℝ) V)
  obtain ⟨hroundL,hroundU⟩ := material_dose_rounding side V p
  constructor <;> nlinarith

end
end FiniteCopyReactor
