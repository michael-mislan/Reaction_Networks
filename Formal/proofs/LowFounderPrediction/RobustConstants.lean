import proofs.LowFounderPrediction.HistoryCertificate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace LowFounderPrediction
noncomputable section

theorem rate_ball_admissible (a : Rates) (h : RateBall a) : Admissible a := by
  obtain ⟨hS,hR⟩ := h
  have hbs := le_abs_self a.bS
  have hds := le_abs_self (a.dS-3/10)
  have hqs := le_abs_self (a.qS-1/1000)
  have hdr := le_abs_self a.dR
  have hbr := le_abs_self (a.bR-1/10)
  have hqr := le_abs_self (a.qR-1/100000)
  have hds' := neg_le_abs (a.dS-3/10)
  have hbr' := neg_le_abs (a.bR-1/10)
  constructor
  · linarith
  · linarith [abs_nonneg a.bS, abs_nonneg (a.qS-1/1000)]
  · unfold amax
    linarith
  · linarith [abs_nonneg a.dR, abs_nonneg (a.qR-1/100000)]

def horizon : NNReal := ⟨(100000/10001)*Real.log 2, by positivity⟩

theorem horizon_le_seven : (horizon : ℝ) ≤ 7 := by
  have h := Real.sum_range_sub_log_div_le (x := (1/3 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  have hh := (abs_le.mp h).2
  have hlog : Real.log 2 ≤ 7/10 := by linarith
  change (100000/10001)*Real.log 2 ≤ 7
  linarith

theorem exponential_bounds :
    1993/4000 ≤ Real.exp (-amax*(horizon : ℝ)) ∧
      Real.exp (-amax*(horizon : ℝ)) ≤ 1/2 := by
  have heq : -amax*(horizon : ℝ) = -Real.log 2-(horizon : ℝ)/2000 := by
    change -(10051/100000)*((100000/10001)*Real.log 2) =
      -Real.log 2-((100000/10001)*Real.log 2)/2000
    ring
  have he : Real.exp (-amax*(horizon : ℝ)) =
      (1/2)*Real.exp (-(horizon : ℝ)/2000) := by
    calc
      _ = Real.exp (-Real.log 2)*Real.exp (-(horizon : ℝ)/2000) := by
        rw [← Real.exp_add]
        congr 1
        rw [heq]
        ring
      _ = _ := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hlow := Real.add_one_le_exp (-(horizon : ℝ)/2000)
  have hup : Real.exp (-(horizon : ℝ)/2000) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := horizon.property; linarith)
  rw [he]
  constructor <;> linarith [horizon_le_seven]

def resistantLower : ℝ := (1993/4000)*(1+c/2+c^2/4)

theorem resistant_value_lower : resistantLower ≤ value horizon 2 := by
  obtain ⟨hl,hu⟩ := exponential_bounds
  have hc : 0 ≤ c := by norm_num [c]
  have he : 0 ≤ Real.exp (-amax*(horizon : ℝ)) := (Real.exp_pos _).le
  have hz : 1/2 ≤ 1-Real.exp (-amax*(horizon : ℝ)) := by linarith
  have hsq : (1/4 : ℝ) ≤ (1-Real.exp (-amax*(horizon : ℝ)))^2 := by nlinarith
  have hsum : 1+c/2+c^2/4 ≤
      1+c*(1-Real.exp (-amax*(horizon : ℝ)))+
      c^2*(1-Real.exp (-amax*(horizon : ℝ)))^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hz hc,
      mul_le_mul_of_nonneg_left hsq (sq_nonneg c)]
  have hm := (mul_le_mul_of_nonneg_right hl
    (by positivity : 0 ≤ 1+c/2+c^2/4)).trans
      (mul_le_mul_of_nonneg_left hsum he)
  dsimp [resistantLower]
  norm_num [value]
  simp only [neg_mul] at hm
  nlinarith only [hm]

theorem history_mixture_constant (p : ℝ) (_hp0 : 0 ≤ p) (hp : p ≤ 5/24+1/1000) :
    (57461421889141/60212040602000 : ℝ)+11/1000 ≤
      (1-p)*sensitiveLower+p*resistantLower := by
  norm_num [sensitiveLower, resistantLower, c] at *
  linarith

end
end LowFounderPrediction
