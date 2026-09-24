import proofs.FiniteReservoir.FiniteModel
import proofs.FiniteCopyReactor.ResidencePotential

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

open FiniteCopyReactor (residencePotential residence_potential_nonneg)

/-- Capping pays an exponentially small source at the upper threshold, so the
positive-drift estimate is needed only below that threshold. -/
theorem residence_potential_generator (N : Counts) (V : ℕ) (r alpha beta : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hbox : RateBox alpha beta) (hc : resourceGood N V) :
    generator N V r alpha beta (residencePotential V) ≤
      (3000*(V:ℝ))*Real.exp (-3*(V:ℝ)/5000+9/500) := by
  let R := internalRate N V r alpha beta
  have hn (j) : 0 ≤ R j := internal_nonneg N V r alpha beta hV
    (by linarith) hbox.alpha_nonneg hbox.beta_nonneg j
  have ht : (∑ j,R j) ≤ 3000*(V:ℝ) :=
    total_rate_bound N V r alpha beta hV (by linarith) hr' hbox hc
  let c := Real.exp (-3*(V:ℝ)/5000)
  let b := Real.exp (-3*(V:ℝ)/5000+9/500)
  have hcb : c ≤ b := Real.exp_le_exp.mpr (by linarith)
  by_cases hy : weightedCount N ≤ (3/50)*(V:ℝ)
  · have he : residencePotential V N = Real.exp (-weightedCount N/100) := by
      apply max_eq_left
      apply Real.exp_le_exp.mpr
      linarith
    have hp (X : Counts) : residencePotential V X ≤ Real.exp (-weightedCount X/100)+c := by
      apply max_le
      · exact le_add_of_nonneg_right (Real.exp_pos _).le
      · exact le_add_of_nonneg_left (Real.exp_pos _).le
    have hsum : generator N V r alpha beta (residencePotential V) ≤
        generator N V r alpha beta (fun X => Real.exp (-weightedCount X/100)) + (∑ j,R j)*c := by
      unfold generator
      rw [Finset.sum_mul,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      rw [he]
      have hh := mul_le_mul_of_nonneg_left (hp (competitionNext N j)) (hn j)
      dsimp [R] at *
      nlinarith
    have hg := corridor_stock_exponential N V r alpha beta (1/100) hV hr hr' hbox hc hy
      (by norm_num) (by norm_num)
    have hz : generator N V r alpha beta
        (fun X => Real.exp (-weightedCount X/100)) ≤ 0 := by
      have hh : (fun X => Real.exp (-(1/100)*weightedCount X)) =
          (fun X => Real.exp (-weightedCount X/100)) := by funext X; congr 1; ring
      rw [hh] at hg
      exact hg.trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (by nlinarith [weightedCount_nonneg N]))
    have hm := mul_le_mul ht hcb (Real.exp_pos _).le (by positivity : 0 ≤ 3000*(V:ℝ))
    change _ ≤ 3000*(V:ℝ)*b
    linarith
  · have hp (j) (hj : R j ≠ 0) : residencePotential V (competitionNext N j) ≤ b := by
      have hactual := weighted_actual_jump N (competitionBase j)
        (internal_support N V r alpha beta j hj)
      have hjump := (abs_le.mp (weightedJump_bound (competitionBase j))).1
      apply max_le
      · apply Real.exp_le_exp.mpr
        change -weightedCount (countNext N (competitionBase j))/100 ≤ _
        linarith
      · exact hcb
    have hh : generator N V r alpha beta (residencePotential V) ≤ (∑ j,R j)*b := by
      unfold generator
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : R j = 0
      · change R j * _ ≤ R j*b
        simp only [hj,zero_mul,le_refl]
      · apply mul_le_mul_of_nonneg_left _ (hn j)
        linarith [hp j hj,residence_potential_nonneg V N]
    exact hh.trans (mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le)

end
end FiniteReservoir
