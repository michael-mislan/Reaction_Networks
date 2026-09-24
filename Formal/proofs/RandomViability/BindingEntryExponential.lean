import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace RandomViability.Binding
open scoped BigOperators

/-- Certified quadratic bound at the largest weighted dilution jump. -/
theorem exp_small_quadratic (x : ℝ) (hx : |x| ≤ 9/50) :
    Real.exp x ≤ 1+x+(3/5)*x^2 := by
  have h := Real.exp_bound (x := x) (by linarith : |x| ≤ 1) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  have hc : |x|^3 ≤ (9/50)*x^2 := by
    have hh := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
    simpa [pow_succ,sq_abs,mul_comm] using hh
  have he := (abs_le.mp h).2
  nlinarith

/-- Local exponential-generator inequality used by the prospective Riccati
entry argument. No entry probability is assumed or concluded here. -/
theorem entry_exponential_raw {ι : Type*} [Fintype ι]
    (rate jump : ι → ℝ) (Y epsV s : ℝ)
    (hr : ∀ j, 0 ≤ rate j) (hj : ∀ j, |jump j| ≤ 9/5)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/10)
    (hg : (39/100)*Y+(16/25)*epsV ≤ ∑ j,rate j*jump j)
    (hq : (∑ j,rate j*(jump j)^2) ≤ 5*Y+(25/16)*epsV) :
    (∑ j,rate j*(Real.exp (-s*jump j)-1)) ≤
      -(39/100*s-3*s^2)*Y-(16/25*s-15/16*s^2)*epsV := by
  have hsum : (∑ j,rate j*(Real.exp (-s*jump j)-1)) ≤
      -s*(∑ j,rate j*jump j)+(3/5)*s^2*(∑ j,rate j*(jump j)^2) := by
    calc
      _ ≤ ∑ j,rate j*(-s*jump j+(3/5)*s^2*(jump j)^2) := by
        apply Finset.sum_le_sum
        intro j _
        have ha : |-s*jump j| ≤ 9/50 := by
          rw [abs_mul,abs_neg,abs_of_nonneg hs]
          exact (mul_le_mul hs1 (hj j) (abs_nonneg _) (by norm_num)).trans (by norm_num)
        have he := exp_small_quadratic (-s*jump j) ha
        apply mul_le_mul_of_nonneg_left _ (hr j)
        nlinarith
      _ = _ := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hg' := mul_le_mul_of_nonneg_left hg hs
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ (3/5)*s^2 by positivity)
  nlinarith

theorem entry_exponential_drift {ι : Type*} [Fintype ι]
    (rate jump : ι → ℝ) (Y epsV s : ℝ)
    (hr : ∀ j, 0 ≤ rate j) (hj : ∀ j, |jump j| ≤ 9/5)
    (hY : 0 ≤ Y) (hepsV : 0 ≤ epsV) (hs : 0 ≤ s) (hs1 : s ≤ 1/10)
    (hg : (39/100)*Y+(16/25)*epsV ≤ ∑ j,rate j*jump j)
    (hq : (∑ j,rate j*(jump j)^2) ≤ 5*Y+(25/16)*epsV) :
    (∑ j,rate j*(Real.exp (-s*jump j)-1)) ≤
      -(3/10*s-3*s^2)*Y-(1/2)*epsV*s := by
  have h := entry_exponential_raw rate jump Y epsV s hr hj hs hs1 hg hq
  have hsquare : s^2 ≤ s/10 := by nlinarith
  have he := mul_le_mul_of_nonneg_left hsquare hepsV
  have hy := mul_nonneg hs hY
  nlinarith

/-- Sharper immigration coefficient for the exact capped discrete schedule. -/
theorem entry_exponential_strong {ι : Type*} [Fintype ι]
    (rate jump : ι → ℝ) (Y epsV s : ℝ)
    (hr : ∀ j, 0 ≤ rate j) (hj : ∀ j, |jump j| ≤ 9/5)
    (hY : 0 ≤ Y) (hepsV : 0 ≤ epsV) (hs : 0 ≤ s) (hs1 : s ≤ 2/25)
    (hg : (39/100)*Y+(16/25)*epsV ≤ ∑ j,rate j*jump j)
    (hq : (∑ j,rate j*(jump j)^2) ≤ 5*Y+(25/16)*epsV) :
    (∑ j,rate j*(Real.exp (-s*jump j)-1)) ≤
      -(3/10*s-3*s^2)*Y-(14/25)*epsV*s := by
  have h := entry_exponential_raw rate jump Y epsV s hr hj hs (by linarith) hg hq
  have hsquare : s^2 ≤ (2/25)*s := by nlinarith
  have he := mul_le_mul_of_nonneg_left hsquare hepsV
  have hy := mul_nonneg hs hY
  nlinarith

end RandomViability.Binding
