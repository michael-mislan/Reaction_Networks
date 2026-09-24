import proofs.RAF1519.Refinement.CountPulse
import proofs.RAF1519.Refinement.PulsePreparationMargins

namespace RAF1519.Refinement
noncomputable section
open Classical
set_option maxHeartbeats 10000

theorem pulse_refill_feasible (p : Intervention) (food : Fin 2) :
    49/200 ≤ 1-p.q+(if food=0 then p.eU else p.eW) ∧
    1-p.q+(if food=0 then p.eU else p.eW) ≤ 151/200 := by
  have hh := ProductiveRecovery.food_feasible p.toIntervention
  by_cases hf : food=0
  · simp only [if_pos hf]
    exact ⟨hh.1,hh.2.1⟩
  · simp only [if_neg hf]
    exact hh.2.2

theorem pulseDose_rounding (V : ℕ) (p : Intervention) (food : Fin 2) :
    (V:ℝ)*(1-p.q+(if food=0 then p.eU else p.eW))-1 < (pulseDose V p food:ℝ) ∧
    (pulseDose V p food:ℝ) ≤ (V:ℝ)*(1-p.q+(if food=0 then p.eU else p.eW)) := by
  have h := pulse_refill_feasible p food
  constructor
  · have hh := Nat.lt_floor_add_one ((V:ℝ)*(1-p.q+(if food=0 then p.eU else p.eW)))
    unfold pulseDose
    linarith
  · exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (by linarith [h.1]))

theorem pulseDose_budget (V : ℕ) (p : Intervention) (food : Fin 2) :
    (pulseDose V p food:ℝ) ≤ (151/200)*(V:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (pulse_refill_feasible p food).2 (Nat.cast_nonneg (α := ℝ) V)
  linarith [(pulseDose_rounding V p food).2]

end
end RAF1519.Refinement
