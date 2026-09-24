import proofs.FiniteCopyReactor.Residence

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

def clampedResidence (V : ℝ) (N : Counts) : ℝ :=
  min 1 (Real.exp (V/2000)*residencePotential V N)

theorem clamped_residence_bounds (V : ℝ) (N : Counts) :
    0 ≤ clampedResidence V N ∧ clampedResidence V N ≤ 1 := by
  constructor
  · exact le_min (by norm_num) (mul_nonneg (Real.exp_pos _).le (residence_potential_nonneg V N))
  · exact min_le_left _ _

theorem clamped_residence_high (V : ℝ) (N : Counts) (h : (3/50)*V ≤ weightedCount N) :
    clampedResidence V N ≤ Real.exp (-V/10000) := by
  have he : residencePotential V N=Real.exp (-3*V/5000) := by
    apply max_eq_right
    apply Real.exp_le_exp.mpr
    linarith
  unfold clampedResidence
  rw [he]
  apply (min_le_right _ _).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

theorem clamped_residence_low (V : ℝ) (N : Counts) (h : weightedCount N ≤ V/20) :
    clampedResidence V N=1 := by
  apply min_eq_left
  have he : 1 ≤ Real.exp (V/2000)*Real.exp (-weightedCount N/100) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    linarith
  exact he.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le)

theorem clamped_residence_generator (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (hc : resourceGood N V) :
    competitionGenerator N V (1/500000000) (1/10) r d (clampedResidence V) ≤
      (3000*(V:ℝ))*Real.exp (-(V:ℝ)/10000+9/500) := by
  have hn (j) := competitionRate_nonneg N V (1/500000000) (1/10) r d hV
    (by norm_num) (by norm_num) (by linarith) hd j
  by_cases h : 1 ≤ Real.exp ((V:ℝ)/2000)*residencePotential V N
  · have hz : competitionGenerator N V (1/500000000) (1/10) r d (clampedResidence V) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j _
      apply mul_nonpos_of_nonneg_of_nonpos (hn j)
      unfold clampedResidence
      rw [min_eq_left h]
      exact sub_nonpos.mpr (min_le_left _ _)
    exact hz.trans (by positivity)
  · have hh : competitionGenerator N V (1/500000000) (1/10) r d (clampedResidence V) ≤
        Real.exp ((V:ℝ)/2000)*competitionGenerator N V (1/500000000) (1/10) r d (residencePotential V) := by
      unfold competitionGenerator
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have he : clampedResidence V N=Real.exp ((V:ℝ)/2000)*residencePotential V N :=
        min_eq_right (le_of_not_ge h)
      rw [he]
      have hm := mul_le_mul_of_nonneg_left
        (min_le_right (1:ℝ) (Real.exp ((V:ℝ)/2000)*residencePotential V (competitionNext N j))) (hn j)
      change _ ≤ _ at hm
      dsimp [clampedResidence]
      nlinarith
    have hg := hh.trans (mul_le_mul_of_nonneg_left
      (residence_potential_generator N V r d hV hr hr' hd hd' hc) (Real.exp_pos _).le)
    apply hg.trans_eq
    rw [mul_left_comm,← Real.exp_add]
    congr 2
    ring

end
end FiniteCopyReactor
