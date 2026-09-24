import proofs.RandomViability.ProductiveConcrete
import proofs.RandomViability.ProductiveVolumeAsymptotics

namespace RandomViability
open Filter Topology
noncomputable section
set_option maxHeartbeats 50000

theorem productive_beta_log_eq (V : ℕ) (hV : 40 ≤ V) :
    Real.log (productiveBeta V) =
      -((3*((V+9)/10)+1 : ℕ) : ℝ)*(Real.log 1000000000+Real.log (((V+9)/10 : ℕ) : ℝ))
      -4800000*(V : ℝ) := by
  let m := (V+9)/10
  have hm : 0 < m := (productive_volume_rounding V hV).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : productiveEpsilon*productiveWaitWidth m = (1000000000*(m : ℝ))⁻¹ := by
    unfold productiveEpsilon productiveWaitWidth
    field_simp
    norm_num
  change Real.log ((productiveEpsilon*productiveWaitWidth m)^(3*m+1)*
    Real.exp (-4800000*(V : ℝ))) = _
  rw [hb,Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_pow,
    Real.log_exp,Real.log_inv,Real.log_mul (by norm_num) hmR.ne']
  push_cast
  ring

theorem productive_beta_log_bound (V : ℕ) (hV : 40 ≤ V) :
    0 ≤ -Real.log (productiveBeta V) ∧
    -Real.log (productiveBeta V) ≤
      (4*Real.log 1000000000+4800000)*(V : ℝ)+4*(V : ℝ)*Real.log (V : ℝ) := by
  let m := (V+9)/10
  have hr := productive_volume_rounding V hV
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hr.1
  have hmV : (m : ℝ) ≤ V := by exact_mod_cast (show m ≤ V by dsimp [m]; omega)
  have hk : ((3*m+1 : ℕ) : ℝ) ≤ 4*(V : ℝ) := by
    exact_mod_cast (show 3*m+1 ≤ 4*V by dsimp [m]; omega)
  have hlm := Real.log_nonneg hm1
  have hlc : 0 ≤ Real.log (1000000000 : ℝ) := Real.log_nonneg (by norm_num)
  have hlV := Real.log_le_log (by linarith : (0 : ℝ) < m) hmV
  have hlogs : Real.log 1000000000+Real.log (m : ℝ) ≤
      Real.log 1000000000+Real.log (V : ℝ) := by linarith
  have hp := mul_le_mul hk hlogs
    (add_nonneg hlc hlm) (by positivity : 0 ≤ 4*(V : ℝ))
  have heq : -Real.log (productiveBeta V) =
      ((3*m+1 : ℕ) : ℝ)*(Real.log 1000000000+Real.log (m : ℝ))+4800000*(V : ℝ) := by
    rw [productive_beta_log_eq V hV]
    dsimp [m]
    ring
  rw [heq]
  constructor
  · exact add_nonneg (mul_nonneg (by positivity) (add_nonneg hlc hlm)) (by positivity)
  · nlinarith

/-- The complete paid-path prefactor is subexponential in polymer horizon
under the declared joint volume scaling. -/
theorem productive_beta_log_negligible :
    Tendsto (fun n => Real.log (productiveBeta (productiveVolume n))/(n : ℝ)) atTop (𝓝 0) := by
  let C := 4*Real.log (1000000000 : ℝ)+4800000
  have hl := ((productive_volume_div_nat.const_mul C).add
    (productive_volume_log_div_nat.const_mul 4)).neg
  simp only [mul_zero,zero_add,neg_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards with n
    have hh := (productive_beta_log_bound (productiveVolume n) (productive_volume_ge n)).2
    have hd := div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ n by positivity)
    convert neg_le_neg hd using 1 <;> dsimp [C] <;> ring
  · filter_upwards with n
    have hh := (productive_beta_log_bound (productiveVolume n) (productive_volume_ge n)).1
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

end
end RandomViability
