import proofs.ProductiveRecovery.StrongGrowth
import proofs.ProductiveRecovery.WithdrawalRefill

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery

/-- Interior stock target, uniformly on the original material corridor. -/
theorem interior_guarded_growth (r d : ℝ) (c : State) (hc : Nonneg c)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : 9/10 ≤ A c) (hB : 9/10 ≤ B c) (hY : Y c ≤ 3/50) :
    (2/3)*Y c ≤ Y (field r d c) := by
  have h := parameterized_drift r d (3/50) c hc hr' hd' hA hB hY
  have hi : 0 ≤ ((1/500000000)+d*(1/8000000000))*c 0*c 1 :=
    mul_nonneg (mul_nonneg (by positivity) (hc 0)) (hc 1)
  have hz : 0 ≤ (r/5-19/5)*c 5 := mul_nonneg (by linarith) (hc 5)
  norm_num at h
  linarith [hc 2, hc 3, hc 4]

/-- Sharper pulse means for the routine restart band; not a random-path bound. -/
theorem routine_pulse_material (p : Intervention) (c : State) (hc : Nonneg c)
    (ha : 159/160 ≤ A c ∧ A c ≤ 161/160)
    (hb : 159/160 ≤ B c ∧ B c ≤ 161/160) :
    (31213/32000 ≤ A (pulse p c) ∧ A (pulse p c) ≤ 3231/3200) ∧
    (31213/32000 ≤ B (pulse p c) ∧ B (pulse p c) ≤ 3231/3200) := by
  have h0 := retained_bounds p c hc 0
  have h1 := retained_bounds p c hc 1
  have h2 := retained_bounds p c hc 2
  have h3 := retained_bounds p c hc 3
  have h4 := retained_bounds p c hc 4
  have h5 := retained_bounds p c hc 5
  have hq : 0 ≤ p.q := by linarith [p.q_lower]
  have haL := mul_le_mul_of_nonneg_left ha.1 (mul_nonneg hq (by norm_num : (0:ℝ) ≤ 49/50))
  have haU := mul_le_mul_of_nonneg_left ha.2 hq
  have hbL := mul_le_mul_of_nonneg_left hb.1 (mul_nonneg hq (by norm_num : (0:ℝ) ≤ 49/50))
  have hbU := mul_le_mul_of_nonneg_left hb.2 hq
  dsimp [A,B] at haL haU hbL hbU
  norm_num [A,B,pulse,Fin.ext_iff]
  constructor <;> constructor <;>
    nlinarith [p.q_upper,p.eU_lower,p.eU_upper,p.eW_lower,p.eW_upper]

end
end FiniteCopyReactor
