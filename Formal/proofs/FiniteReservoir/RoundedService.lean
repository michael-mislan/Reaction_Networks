import proofs.FiniteReservoir.JointTails

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical

theorem gross_cycle_rounded_upper (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
     (N : BoxState V M) :
    supplyCycle .gross V M p hV
      (MarkedKernel.eventIndicator {a | (V:ℝ)/5-1 ≤ a.2}) N 0 ≤ Real.exp (-(V:ℝ)/2000) := by
  have h := supply_cycle_upper .gross V M p hV (1/20) ((V:ℝ)/5-1) (by norm_num) N 0
  apply h.trans
  apply Real.exp_le_exp.mpr
  dsimp [supplyRateCap]
  have he := exp_small_quadratic (1/20:ℝ) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left he hV.le
  have hv : (1000000:ℝ) ≤ V := by exact_mod_cast hlarge
  nlinarith

theorem joint_rounded_gross_tail (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    
    (N : BoxState V M) (doseU doseW : ℝ) :
    jointCycle V M p hV
      (fun X => if (V:ℝ)/5-1 ≤ X.2 4 then 1 else 0) N (initialCounters doseU doseW) ≤
      Real.exp (-(V:ℝ)/2000) := by
  have he := joint_cycle_supply_marginal .gross V M p hV
    (MarkedKernel.eventIndicator {a | (V:ℝ)/5-1 ≤ a.2}) N (initialCounters doseU doseW)
  have h := gross_cycle_rounded_upper V M p hV hlarge N
  convert he.le.trans h using 1

end
end FiniteReservoir
