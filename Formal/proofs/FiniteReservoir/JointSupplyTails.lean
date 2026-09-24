import proofs.FiniteReservoir.JointTails

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical

theorem joint_foodU_tail (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (N : BoxState V M) (doseU doseW : ℝ) (hu : doseU ≤ (151/200)*(V:ℝ)) :
    jointCycle V M p hV
      (fun X => if 5*(V:ℝ) ≤ X.2 2 then 1 else 0) N (initialCounters doseU doseW) ≤
      Real.exp (-(V:ℝ)/300) := by
  have he := joint_cycle_supply_marginal .foodU V M p hV
    (MarkedKernel.eventIndicator {a | 5*(V:ℝ) ≤ a.2}) N (initialCounters doseU doseW)
  have h := food_cycle_upper .foodU (Or.inl rfl) V M p hV N doseU hu
  convert he.le.trans h using 1

theorem joint_foodW_tail (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (N : BoxState V M) (doseU doseW : ℝ) (hw : doseW ≤ (151/200)*(V:ℝ)) :
    jointCycle V M p hV
      (fun X => if 5*(V:ℝ) ≤ X.2 3 then 1 else 0) N (initialCounters doseU doseW) ≤
      Real.exp (-(V:ℝ)/300) := by
  have he := joint_cycle_supply_marginal .foodW V M p hV
    (MarkedKernel.eventIndicator {a | 5*(V:ℝ) ≤ a.2}) N (initialCounters doseU doseW)
  have h := food_cycle_upper .foodW (Or.inr rfl) V M p hV N doseW hw
  convert he.le.trans h using 1

theorem joint_gross_tail (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (N : BoxState V M) (doseU doseW : ℝ) :
    jointCycle V M p hV
      (fun X => if (V:ℝ)/5 ≤ X.2 4 then 1 else 0) N (initialCounters doseU doseW) ≤
      Real.exp (-(V:ℝ)/2000) := by
  have he := joint_cycle_supply_marginal .gross V M p hV
    (MarkedKernel.eventIndicator {a | (V:ℝ)/5 ≤ a.2}) N (initialCounters doseU doseW)
  have h := gross_cycle_upper V M p hV N
  convert he.le.trans h using 1

end
end FiniteReservoir
