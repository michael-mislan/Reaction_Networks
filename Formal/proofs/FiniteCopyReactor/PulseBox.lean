import proofs.FiniteCopyReactor.PulseMaterialProbability
import proofs.FiniteCopyReactor.MaterialModel

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

theorem categoryCounts_le (N : Counts) (o : PulseOutcome N) (a : Fin 3) (i : Fin 6) :
    categoryCounts N o a i ≤ N i := by
  unfold categoryCounts
  calc
    _ ≤ ∑ _k : Fin (N i), 1 := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs <;> omega
    _ = _ := by simp

theorem restart_count_cap (N : Counts) (V : ℕ) (hN : Restart V N) (i : Fin 6) :
    (N i:ℝ) ≤ (161/160)*(V:ℝ) := by
  apply (count_le_units N i).trans
  apply max_le
  · linarith [hN.2.1]
  · linarith [hN.2.2.2.1]

/-- Every actual pulse outcome fits the outer box, not merely good outcomes. -/
theorem postPulse_in_box (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (o : PulseOutcome N) (i : Fin 6) : postPulseCounts N V p o i < 3*V+3 := by
  have hu : doseU V p ≤ V := by
    have h := (pulse_food_budget V p).1
    have hv := Nat.cast_nonneg (α := ℝ) V
    have hh : (doseU V p:ℝ) ≤ (V:ℝ) := by linarith
    exact_mod_cast hh
  have hw : doseW V p ≤ V := by
    have h := (pulse_food_budget V p).2
    have hv := Nat.cast_nonneg (α := ℝ) V
    have hh : (doseW V p:ℝ) ≤ (V:ℝ) := by linarith
    exact_mod_cast hh
  have hpost : postPulseCounts N V p o i ≤ N i+V := by
    unfold postPulseCounts
    have hc := categoryCounts_le N o 0 i
    split_ifs <;> omega
  have hr : (postPulseCounts N V p o i:ℝ) ≤ (N i:ℝ)+(V:ℝ) := by exact_mod_cast hpost
  have hh : (postPulseCounts N V p o i:ℝ) < 3*(V:ℝ)+3 := by
    linarith [restart_count_cap N V hN i,Nat.cast_nonneg (α := ℝ) V]
  exact_mod_cast hh

def postPulseBox (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (o : PulseOutcome N) : BoxCounts V :=
  fun i => ⟨postPulseCounts N V p o i,postPulse_in_box N V p hN o i⟩

theorem postPulseBox_counts (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (o : PulseOutcome N) : boxCounts (postPulseBox N V p hN o) = postPulseCounts N V p o := rfl

end
end FiniteCopyReactor
