import proofs.FiniteCopyReactor.SupplySource
import proofs.FiniteCopyReactor.MarkedUpper

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators NNReal

def supplyModel (stopStock : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hd : 0 ≤ d) :=
  if stopStock then residenceModel V r d hV hr hd else materialModel V r d hV hr hd

theorem supply_total_bound (b : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (supplyModel b V r d hV hr hd).total N ≤ 3000*(V:ℝ) := by
  cases b
  · exact material_total_bound V r d hV hr hr' hd hd' N
  · exact residence_total_bound V r d hV hr hr' hd hd' N

def supplyKernel (b : Bool) (k : SupplyKind) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :=
  (supplyModel b V r d hV hr hd).withMarks (supplyMark k) (3000*(V:ℝ))
    (by positivity) (supply_total_bound b V r d hV hr hr' hd hd')

theorem supply_model_intensity (b : Bool) (k : SupplyKind) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (∑ j,(supplyModel b V r d hV hr hd).rate N j*supplyMark k j) ≤ supplyRateCap k*(V:ℝ) := by
  cases b with
  | false =>
    change (∑ j,(if resourceGood (boxCounts N) V then _ else 0)*_) ≤ _
    by_cases h : resourceGood (boxCounts N) V
    · simp only [if_pos h]
      exact supply_intensity_bound k (boxCounts N) V r d hV hd hd' h
    · simp only [if_neg h,zero_mul,Finset.sum_const_zero]
      exact mul_nonneg (supply_rate_cap_nonneg k) hV.le
  | true =>
    change (∑ j,(if residenceActive V N then _ else 0)*_) ≤ _
    by_cases h : residenceActive V N
    · simp only [if_pos h]
      exact supply_intensity_bound k (boxCounts N) V r d hV hd hd' h.1
    · simp only [if_neg h,zero_mul,Finset.sum_const_zero]
      exact mul_nonneg (supply_rate_cap_nonneg k) hV.le

theorem supply_exponential_step (b : Bool) (k : SupplyKind) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (s : ℝ) (hs : 0 ≤ s)
    (N : BoxCounts V) (z : ℝ) :
    (supplyKernel b k V r d hV hr hr' hd hd').step (fun _ w => Real.exp (s*w)) N z ≤
      (1+(supplyRateCap k/3000)*(Real.exp s-1))*Real.exp (s*z) := by
  let P := supplyKernel b k V r d hV hr hr' hd hd'
  have hm (j) : P.mark j=0 ∨ P.mark j=1 := by
    cases j with
    | none => exact Or.inl rfl
    | some j => exact supply_mark_binary k j
  apply bernoulli_mark_step P hm (supplyRateCap k/3000) s hs
  intro X
  simp only [P,supplyKernel,FiniteJumpModel.withMarks,Fintype.sum_option,mul_zero,zero_add,
    div_mul_eq_mul_div,← Finset.sum_div]
  apply (div_le_iff₀ (show 0 < 3000*(V:ℝ) by positivity)).mpr
  have h := supply_model_intensity b k V r d hV hr hd hd' X
  convert h using 1
  ring

end
end FiniteCopyReactor
