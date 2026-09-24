import proofs.FiniteCopyReactor.JointTails

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem joint_foodU_tail (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (doseU doseW : ℝ) (hu : doseU ≤ (151/200)*(V:ℝ)) :
    jointCycle V r d hV hr hr' hd hd'
      (fun X => if 5*(V:ℝ) ≤ X.2 2 then 1 else 0) N (initialCounters doseU doseW) ≤
      Real.exp (-(V:ℝ)/300) := by
  have he := joint_cycle_supply_marginal .foodU V r d hV hr hr' hd hd'
    (MarkedKernel.eventIndicator {a | 5*(V:ℝ) ≤ a.2}) N (initialCounters doseU doseW)
  have h := food_cycle_upper .foodU (Or.inl rfl) V r d hV hr hr' hd hd' N doseU hu
  convert he.le.trans h using 1

theorem joint_foodW_tail (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (doseU doseW : ℝ) (hw : doseW ≤ (151/200)*(V:ℝ)) :
    jointCycle V r d hV hr hr' hd hd'
      (fun X => if 5*(V:ℝ) ≤ X.2 3 then 1 else 0) N (initialCounters doseU doseW) ≤
      Real.exp (-(V:ℝ)/300) := by
  have he := joint_cycle_supply_marginal .foodW V r d hV hr hr' hd hd'
    (MarkedKernel.eventIndicator {a | 5*(V:ℝ) ≤ a.2}) N (initialCounters doseU doseW)
  have h := food_cycle_upper .foodW (Or.inr rfl) V r d hV hr hr' hd hd' N doseW hw
  convert he.le.trans h using 1

theorem joint_gross_tail (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (doseU doseW : ℝ) :
    jointCycle V r d hV hr hr' hd hd'
      (fun X => if (V:ℝ)/5 ≤ X.2 4 then 1 else 0) N (initialCounters doseU doseW) ≤
      Real.exp (-(V:ℝ)/2000) := by
  have he := joint_cycle_supply_marginal .gross V r d hV hr hr' hd hd'
    (MarkedKernel.eventIndicator {a | (V:ℝ)/5 ≤ a.2}) N (initialCounters doseU doseW)
  have h := gross_cycle_upper V r d hV hr hr' hd hd' N
  convert he.le.trans h using 1

end
end FiniteCopyReactor
