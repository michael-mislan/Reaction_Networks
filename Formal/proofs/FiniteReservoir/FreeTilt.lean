import proofs.FiniteReservoir.FreeRow
import proofs.FiniteCopyReactor.TrackedOccupation

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped BigOperators

def freeTracked (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :=
  trackedOccupation (residenceMarked V M p hV)
    (FiniteKernel.eventIndicator (LowFreeActive V M))

def freeTilt (V M : ℕ) (X : BoxState V M × ℝ) (z : ℝ) : ℝ :=
  if residenceActive V X.1.1 then Real.exp (-(1/1000)*(z+X.2/3000000)) else 0

theorem free_tilt_step (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (X : BoxState V M × ℝ) (z : ℝ) :
    (freeTracked V M p hV).step (freeTilt V M) X z ≤
      Real.exp (-(33/100000000000:ℝ))*freeTilt V M X z := by
  let P := residenceMarked V M p hV
  let b := FiniteKernel.eventIndicator (LowFreeActive V M) X.1
  by_cases hc : residenceActive V X.1.1
  · have hpoint (j) : freeTilt V M (P.next X.1 j,X.2+b) (z+P.mark j) ≤
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
    have hrw := mul_le_mul_of_nonneg_left (corrected_free_row V M p hV X.1 hc)
      (Real.exp_pos (-(1/1000)*(z+X.2/3000000))).le
    have hb := hh.trans hrw
    change _ ≤ _ at hb
    simpa only [freeTilt,if_pos hc,mul_comm] using hb
  · change ¬(resourceGood (boxCounts X.1.1) V ∧ (V:ℝ)/20 < weightedCount (boxCounts X.1.1)) at hc
    unfold MarkedKernel.step freeTracked trackedOccupation
    rw [Fintype.sum_option]
    simp only [residenceMarked,FiniteJumpModel.withMarks,residenceModel,model,if_neg hc,
      zero_div,zero_mul,Finset.sum_const_zero,add_zero]
    simp only [freeTilt,residenceActive,if_neg hc,mul_zero,le_refl]

def FreeJointShortfall (V M : ℕ) (K B : ℝ) : Set ((BoxState V M × ℝ) × ℝ) :=
  {s | residenceActive V s.1.1.1 ∧ s.2 ≤ K ∧ s.1.2 ≤ B}

theorem free_joint_discrete (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (K B : ℝ) (n : ℕ) (N : BoxState V M) :
    (freeTracked V M p hV).law n
      (MarkedKernel.eventIndicator (FreeJointShortfall V M K B)) (N,0) 0 ≤
      Real.exp ((1/1000)*(K+B/3000000)-(n:ℝ)*(33/100000000000)) := by
  let P := freeTracked V M p hV
  have hi (X : BoxState V M × ℝ) (z : ℝ) :
      MarkedKernel.eventIndicator (FreeJointShortfall V M K B) X z ≤
        Real.exp ((1/1000)*(K+B/3000000))*freeTilt V M X z := by
    by_cases h : (X,z) ∈ FreeJointShortfall V M K B
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
  have ht := P.law_decay (freeTilt V M) (Real.exp (-(33/100000000000:ℝ)))
    (Real.exp_pos _).le (free_tilt_step V M p hV) n (N,0) 0
  have hz : freeTilt V M (N,0) 0 ≤ 1 := by
    unfold freeTilt
    split_ifs <;> norm_num
  have hb := hh.trans (mul_le_mul_of_nonneg_left (ht.trans
    (mul_le_mul_of_nonneg_left hz (pow_nonneg (Real.exp_pos _).le n))) (Real.exp_pos _).le)
  rw [mul_one,← Real.exp_nat_mul,← Real.exp_add] at hb
  convert hb using 1
  congr 1
  ring

end
end FiniteReservoir
