import proofs.CommonPhysicalRealization.ExporterSource
import Mathlib

namespace CommonPhysicalRealization
noncomputable section

def seedCoefficient (d : ℝ) : ℝ := 1/500000000+d/8000000000

theorem seed_rate (u w : ℕ) (V r d : ℝ) :
    physicalRate ![u,w,0,0,0,0] V r d 1 1 (.inl 0)+
      physicalRate ![u,w,0,0,0,0] V r d 1 1 (.inr 1) =
        seedCoefficient d*(u:ℝ)*(w:ℝ)/V := by
  norm_num [physicalRate,seedCoefficient]
  ring

theorem seed_coefficient_bound (d : ℝ) (hd : 0 ≤ d) (hu : d ≤ 1/25) :
    0 < seedCoefficient d ∧ seedCoefficient d ≤ 401/200000000000 := by
  dsimp [seedCoefficient]
  constructor <;> linarith

/-- The supporting tangent inequality used under the reference-process integral. -/
theorem survival_tangent (x m : ℝ) :
    Real.exp (-m)*(1+m-x) ≤ Real.exp (-x) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (m-x)) (Real.exp_pos (-m)).le
  rw [← Real.exp_add] at h
  convert h using 1 <;> ring

/-- Given the conventional no-initiation lower bound, this is the necessary size. -/
theorem necessary_seed_size (d V eps : ℝ) (hd : 0 ≤ d) (_heps : 0 < eps)
    (hfailure : Real.exp (-500*seedCoefficient d*V) ≤ eps) :
    Real.log (1/eps)/(500*seedCoefficient d) ≤ V := by
  have ha : 0 < seedCoefficient d := by dsimp [seedCoefficient]; positivity
  have h := Real.log_le_log (Real.exp_pos _) hfailure
  rw [Real.log_exp] at h
  rw [one_div,Real.log_inv]
  apply (div_le_iff₀ (by positivity : 0 < 500*seedCoefficient d)).mpr
  linarith

theorem uniform_necessary_seed_size (d V eps : ℝ) (hd : 0 ≤ d) (hu : d ≤ 1/25)
    (hV : 0 ≤ V) (_heps : 0 < eps)
    (hfailure : Real.exp (-500*seedCoefficient d*V) ≤ eps) :
    (400000000/401)*Real.log (1/eps) ≤ V := by
  have h := Real.log_le_log (Real.exp_pos _) hfailure
  rw [Real.log_exp] at h
  have hm := mul_le_mul_of_nonneg_right (seed_coefficient_bound d hd hu).2 hV
  rw [one_div,Real.log_inv]
  linarith

end
end CommonPhysicalRealization

