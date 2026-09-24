import proofs.RAF1519.Refinement.Pulse

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 10000

def speciesRetention (p : Intervention) : Fin 7 → ℝ :=
  ![p.loss 0,p.loss 1,p.loss 2,p.loss 3,p.loss 4,p.loss 5,p.lossD]

theorem speciesRetention_bounds (p : Intervention) (s : Fin 7) :
    49/50 ≤ speciesRetention p s ∧ speciesRetention p s ≤ 1 := by
  fin_cases s
  all_goals first | exact ⟨p.loss_lower _,p.loss_upper _⟩ | exact ⟨p.lossD_lower,p.lossD_upper⟩

def pulseCategory (p : Intervention) (s : Fin 7) : Fin 3 → ℝ :=
  ![p.q*speciesRetention p s,1-p.q,p.q*(1-speciesRetention p s)]

theorem pulseCategory_nonnegative (p : Intervention) (s : Fin 7) (a : Fin 3) :
    0 ≤ pulseCategory p s a := by
  have hq : 0 ≤ p.q := le_trans (by norm_num) p.q_lower
  have hl : 0 ≤ speciesRetention p s := le_trans (by norm_num) (speciesRetention_bounds p s).1
  fin_cases a
  · exact mul_nonneg hq hl
  · change 0 ≤ 1-p.q
    linarith [p.q_upper]
  · exact mul_nonneg hq (sub_nonneg.mpr (speciesRetention_bounds p s).2)

theorem pulseCategory_total (p : Intervention) (s : Fin 7) : ∑ a, pulseCategory p s a=1 := by
  norm_num [pulseCategory,Fin.sum_univ_succ]
  ring

end
end RAF1519.Refinement
