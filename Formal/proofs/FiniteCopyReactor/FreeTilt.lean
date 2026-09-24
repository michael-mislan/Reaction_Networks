import proofs.FiniteCopyReactor.FreeRow
import proofs.FiniteCopyReactor.TrackedOccupation

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

def freeTracked (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :=
  trackedOccupation (residenceMarked V r d hV hr hr' hd hd')
    (FiniteKernel.eventIndicator (LowFreeActive V))

def freeTilt (V : ℕ) (X : BoxCounts V × ℝ) (z : ℝ) : ℝ :=
  if residenceActive V X.1 then Real.exp (-(1/1000)*(z+X.2/3000000)) else 0

theorem free_tilt_step (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (X : BoxCounts V × ℝ) (z : ℝ) :
    (freeTracked V r d hV hr hr' hd hd').step (freeTilt V) X z ≤
      Real.exp (-(33/100000000000:ℝ))*freeTilt V X z := by
  let P := residenceMarked V r d hV hr hr' hd hd'
  let b := FiniteKernel.eventIndicator (LowFreeActive V) X.1
  by_cases hc : residenceActive V X.1
  · have hpoint (j) : freeTilt V (P.next X.1 j,X.2+b) (z+P.mark j) ≤
        Real.exp (-(1/1000)*(z+X.2/3000000))*
          Real.exp (-(1/1000)*(P.mark j+(1/3000000)*b)) := by
      unfold freeTilt
      split_ifs
      · rw [← Real.exp_add]
        apply le_of_eq
        congr 1
        ring
      · positivity
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hpoint j) (P.nonneg X.1 j))
    have he : (∑ j,P.prob X.1 j*(Real.exp (-(1/1000)*(z+X.2/3000000))*
      Real.exp (-(1/1000)*(P.mark j+(1/3000000)*b)))) =
      Real.exp (-(1/1000)*(z+X.2/3000000))*(∑ j,P.prob X.1 j*
      Real.exp (-(1/1000)*(P.mark j+(1/3000000)*b))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he] at hh
    have hrw := mul_le_mul_of_nonneg_left (corrected_free_row V r d hV hr hr' hd hd' X.1 hc)
      (Real.exp_pos (-(1/1000)*(z+X.2/3000000))).le
    have hb := hh.trans hrw
    change _ ≤ _ at hb
    simpa only [freeTilt,if_pos hc,mul_comm] using hb
  · unfold MarkedKernel.step freeTracked trackedOccupation
    rw [Fintype.sum_option]
    simp only [residenceMarked,FiniteJumpModel.withMarks,residenceModel,if_neg hc,
      zero_div,zero_mul,Finset.sum_const_zero,add_zero]
    simp only [freeTilt,if_neg hc,mul_zero,le_refl]

def FreeJointShortfall (V : ℕ) (K B : ℝ) : Set ((BoxCounts V × ℝ) × ℝ) :=
  {s | residenceActive V s.1.1 ∧ s.2 ≤ K ∧ s.1.2 ≤ B}

theorem free_joint_discrete (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (K B : ℝ) (n : ℕ) (N : BoxCounts V) :
    (freeTracked V r d hV hr hr' hd hd').law n
      (MarkedKernel.eventIndicator (FreeJointShortfall V K B)) (N,0) 0 ≤
      Real.exp ((1/1000)*(K+B/3000000)-(n:ℝ)*(33/100000000000)) := by
  let P := freeTracked V r d hV hr hr' hd hd'
  have hi (X : BoxCounts V × ℝ) (z : ℝ) :
      MarkedKernel.eventIndicator (FreeJointShortfall V K B) X z ≤
        Real.exp ((1/1000)*(K+B/3000000))*freeTilt V X z := by
    by_cases h : (X,z) ∈ FreeJointShortfall V K B
    · rw [MarkedKernel.eventIndicator,if_pos h]
      simp only [freeTilt,if_pos h.1]
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      linarith [h.2.1,h.2.2]
    · rw [MarkedKernel.eventIndicator,if_neg h]
      unfold freeTilt
      split_ifs <;> positivity
  have hh := P.law_mono _ _ hi n (N,0) 0
  rw [P.law_scale] at hh
  have ht := P.law_decay (freeTilt V) (Real.exp (-(33/100000000000:ℝ)))
    (Real.exp_pos _).le (free_tilt_step V r d hV hr hr' hd hd') n (N,0) 0
  have hz : freeTilt V (N,0) 0 ≤ 1 := by
    unfold freeTilt
    split_ifs <;> norm_num
  have hb := hh.trans (mul_le_mul_of_nonneg_left (ht.trans
    (mul_le_mul_of_nonneg_left hz (pow_nonneg (Real.exp_pos _).le n))) (Real.exp_pos _).le)
  rw [mul_one,← Real.exp_nat_mul,← Real.exp_add] at hb
  convert hb using 1
  congr 1
  ring

end
end FiniteCopyReactor
