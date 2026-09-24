import proofs.RandomViability.BindingCompetitionContractModel
import Mathlib.Analysis.Complex.ExponentialBounds

namespace RandomViability.Binding
noncomputable section
open scoped NNReal

theorem competition_exp_hundred : (100000000:ℝ) ≤ Real.exp 100 := by
  have hpow : (2:ℝ)^100 ≤ (Real.exp 1)^100 := by
    gcongr
    exact Real.exp_one_gt_two.le
  have he : Real.exp (100:ℝ)=(Real.exp 1)^100 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  exact (show (100000000:ℝ)≤2^100 by norm_num).trans hpow

theorem competition_duration_large (V : ℕ) (hV : 100000000 ≤ V) :
    (100000000:ℝ) ≤ competitionDuration V := by
  apply competition_exp_hundred.trans (Real.exp_le_exp.mpr ?_)
  have hv : (100000000:ℝ) ≤ V := by exact_mod_cast hV
  linarith

theorem competition_volume_le_duration (V : ℕ) (hV : 100000000 ≤ V) :
    (V:ℝ) ≤ competitionDuration V := by
  let x : ℝ := (V:ℝ)/100000000
  have hv : (100000000:ℝ) ≤ V := by exact_mod_cast hV
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have he : x ≤ Real.exp (x-1) := by linarith [Real.add_one_le_exp (x-1)]
  calc
    (V:ℝ) = 100000000*x := by dsimp [x]; ring
    _ ≤ Real.exp 100*Real.exp (x-1) :=
      mul_le_mul competition_exp_hundred he (by linarith) (Real.exp_pos _).le
    _ = Real.exp (100+(x-1)) := (Real.exp_add _ _).symm
    _ ≤ competitionDuration V := by
      apply Real.exp_le_exp.mpr
      dsimp [x]
      linarith

theorem competition_total_time_upper (V : ℕ) (hV : 100000000 ≤ V) :
    500+competitionDuration V ≤ 2*competitionDuration V := by
  linarith [competition_duration_large V hV]

theorem competition_constant_prefactor (V : ℕ) (hV : 100000000 ≤ V) (c theta : ℝ)
    (_hc : 0 ≤ c) (hc1 : c ≤ 24000) (htheta : theta ≤ 1) :
    c*Real.exp theta ≤ competitionDuration V := by
  have he : Real.exp theta ≤ 3 := (Real.exp_le_exp.mpr htheta).trans Real.exp_one_lt_three.le
  have hh : c*Real.exp theta ≤ (24000:ℝ)*3 := mul_le_mul hc1 he (Real.exp_pos _).le (by norm_num)
  linarith [competition_duration_large V hV]

theorem competition_leak_scalar (V : ℕ) (hV : 100000000 ≤ V) (c theta d : ℝ)
    (hc : 0 ≤ c) (hc1 : 2*c ≤ 24000) (htheta : theta ≤ 1) (hd : 4/1000000 ≤ d) :
    c*(V:ℝ)*(500+competitionDuration V)*Real.exp (theta-d*(V:ℝ)) ≤ Real.exp (-(V:ℝ)/1000000) := by
  have hp := competition_constant_prefactor V hV (2*c) theta (by linarith) hc1 htheta
  have hv := competition_volume_le_duration V hV
  have ht := competition_total_time_upper V hV
  have he : 0 ≤ competitionDuration V := (Real.exp_pos _).le
  calc
    _ = (c*Real.exp theta)*(V:ℝ)*(500+competitionDuration V)*Real.exp (-d*(V:ℝ)) := by
      rw [show theta-d*(V:ℝ)=theta+(-d*(V:ℝ)) by ring,Real.exp_add]
      ring
    _ ≤ (c*Real.exp theta)*(V:ℝ)*(2*competitionDuration V)*Real.exp (-d*(V:ℝ)) := by
      gcongr
    _ = (2*c*Real.exp theta)*(V:ℝ)*competitionDuration V*Real.exp (-d*(V:ℝ)) := by ring
    _ ≤ competitionDuration V*competitionDuration V*competitionDuration V*Real.exp (-d*(V:ℝ)) := by
      gcongr
    _ = Real.exp ((3/1000000-d)*(V:ℝ)) := by
      unfold competitionDuration
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(V:ℝ)/1000000) := by
      apply Real.exp_le_exp.mpr
      nlinarith [show 0 ≤ (V:ℝ) from Nat.cast_nonneg V]

end
end RandomViability.Binding
