import proofs.FiniteReservoir.Residence
import proofs.FiniteCopyReactor.ClampedResidence

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

open FiniteCopyReactor (clampedResidence residencePotential)

theorem clamped_residence_generator (N : Counts) (V : ℕ) (r alpha beta : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hbox : RateBox alpha beta) (hc : resourceGood N V) :
    generator N V r alpha beta (clampedResidence V) ≤
      (3000*(V:ℝ))*Real.exp (-(V:ℝ)/10000+9/500) := by
  have hn (j) := internal_nonneg N V r alpha beta hV (by linarith) hbox.alpha_nonneg hbox.beta_nonneg j
  by_cases h : 1 ≤ Real.exp ((V:ℝ)/2000)*residencePotential V N
  · have hz : generator N V r alpha beta (clampedResidence V) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j _
      apply mul_nonpos_of_nonneg_of_nonpos (hn j)
      unfold clampedResidence
      rw [min_eq_left h]
      exact sub_nonpos.mpr (min_le_left _ _)
    exact hz.trans (by positivity)
  · have hh : generator N V r alpha beta (clampedResidence V) ≤
        Real.exp ((V:ℝ)/2000)*generator N V r alpha beta (residencePotential V) := by
      unfold generator
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
      (residence_potential_generator N V r alpha beta hV hr hr' hbox hc) (Real.exp_pos _).le)
    apply hg.trans_eq
    rw [mul_left_comm,← Real.exp_add]
    congr 2
    ring

end
end FiniteReservoir
