import proofs.FiniteCopyReactor.Entry
import proofs.FiniteCopyReactor.MaterialModel

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

def residencePotential (V : ℝ) (N : Counts) : ℝ :=
  max (Real.exp (-weightedCount N/100)) (Real.exp (-3*V/5000))

theorem residence_potential_nonneg (V : ℝ) (N : Counts) : 0 ≤ residencePotential V N :=
  (Real.exp_pos _).le.trans (le_max_left _ _)

/-- Capping pays an exponentially small source at the upper threshold, so the
positive-drift estimate is needed only below that threshold. -/
theorem residence_potential_generator (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (hc : resourceGood N V) :
    competitionGenerator N V (1/500000000) (1/10) r d (residencePotential V) ≤
      (3000*(V:ℝ))*Real.exp (-3*(V:ℝ)/5000+9/500) := by
  let R := competitionRate N V (1/500000000) (1/10) r d
  have hn (j) : 0 ≤ R j := competitionRate_nonneg N V (1/500000000) (1/10) r d hV
    (by norm_num) (by norm_num) (by linarith) hd j
  have ht : (∑ j,R j) ≤ 3000*(V:ℝ) := by
    apply competition_total_rate_bound N V (1/500000000) (1/10) r d hV
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith)
      (by linarith) hd (by linarith)
    intro i
    linarith [resource_count_cap N V hc i]
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
    have hsum : competitionGenerator N V (1/500000000) (1/10) r d (residencePotential V) ≤
        competitionGenerator N V (1/500000000) (1/10) r d (fun X => Real.exp (-weightedCount X/100)) + (∑ j,R j)*c := by
      unfold competitionGenerator
      rw [Finset.sum_mul,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      rw [he]
      have hh := mul_le_mul_of_nonneg_left (hp (competitionNext N j)) (hn j)
      dsimp [R] at *
      nlinarith
    have hg := corridor_stock_exponential N V r d (1/100) hV hr hr' hd hd' hc hy
      (by norm_num) (by norm_num)
    have hz : competitionGenerator N V (1/500000000) (1/10) r d
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
        (competition_rate_support N V (1/500000000) (1/10) r d j hj)
      have hjump := (abs_le.mp (weightedJump_bound (competitionBase j))).1
      apply max_le
      · apply Real.exp_le_exp.mpr
        change -weightedCount (countNext N (competitionBase j))/100 ≤ _
        linarith
      · exact hcb
    have hh : competitionGenerator N V (1/500000000) (1/10) r d (residencePotential V) ≤ (∑ j,R j)*b := by
      unfold competitionGenerator
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
end FiniteCopyReactor
