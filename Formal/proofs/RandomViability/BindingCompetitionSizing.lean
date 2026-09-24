import proofs.RandomViability.BindingCompetitionTimed

namespace RandomViability.Binding
noncomputable section
open scoped NNReal

theorem competition_timed_error_bound (V : ℕ) (s : ℝ≥0) (m : ℕ) (hV : 100000000 ≤ V)
    (hH : (m:ℝ)+(s:ℝ) ≤ competitionDuration V) :
    competitionTimedRootError V s m ≤ 2*Real.exp (-(2/100000000)*(V:ℝ)) := by
  have hv : (100000000:ℝ) ≤ V := by exact_mod_cast hV
  have hv0 : 0 ≤ (V:ℝ) := Nat.cast_nonneg _
  have ht : 500 ≤ 500+(m:ℝ)+(s:ℝ) := by linarith [s.property,Nat.cast_nonneg (α := ℝ) m]
  have hentry : Real.exp (-(8047/312500000000)*(V:ℝ)) ≤ Real.exp (-(2/100000000)*(V:ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hclock : Real.exp (-3000*(V:ℝ)/500000) ≤ Real.exp (-(V:ℝ)/1000000) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hresource := competition_small_prefactor_tail V hV 4 (1/1000) (by norm_num) (by norm_num)
  have hresource' : 4*Real.exp (-(V:ℝ)/1000) ≤ Real.exp (-(V:ℝ)/1000000) := by
    simpa only [show -(1/1000:ℝ)*(V:ℝ)=-(V:ℝ)/1000 by ring] using hresource
  have hreturn : Real.exp (-(V:ℝ)/62500) ≤ Real.exp (-(V:ℝ)/1000000) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hrleak := competition_leak_scalar V hV 12000 (1/50) (1/2000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htleak := competition_leak_scalar V hV 3000 (18/125) (1/15625) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgroup : (500+competitionDuration V)*(4*resourceSource V+competitionReturnSource V) ≤
      2*Real.exp (-(V:ℝ)/1000000) := by
    have he : (500+competitionDuration V)*(4*resourceSource V+competitionReturnSource V)=
        12000*(V:ℝ)*(500+competitionDuration V)*Real.exp (1/50-(1/2000)*(V:ℝ))+
        3000*(V:ℝ)*(500+competitionDuration V)*Real.exp (18/125-(1/15625)*(V:ℝ)) := by
      unfold resourceSource competitionReturnSource
      rw [show -(V:ℝ)/2000+1/50=1/50-(1/2000)*(V:ℝ) by ring,
        show 18/125-(V:ℝ)/15625=18/125-(1/15625)*(V:ℝ) by ring]
      ring
    rw [he]
    linarith
  have hm : (m:ℝ) ≤ competitionDuration V := by linarith [s.property]
  have hgroupTimed : (500+(m:ℝ)+(s:ℝ))*(4*resourceSource V+competitionReturnSource V) ≤ 2*Real.exp (-(V:ℝ)/1000000) := by
    apply (mul_le_mul_of_nonneg_right (show 500+(m:ℝ)+(s:ℝ) ≤ 500+competitionDuration V by linarith) (by unfold resourceSource competitionReturnSource; positivity)).trans hgroup
  have hm' : (m:ℝ) ≤ (V:ℝ)*(500+competitionDuration V) := by
    have he : 0 ≤ competitionDuration V := (Real.exp_pos _).le
    have hh := mul_nonneg (show 0 ≤ (V:ℝ)-1 by linarith) he
    nlinarith
  have hwindow : (m:ℝ)*Real.exp (1/8-(13/1080000)*(V:ℝ)) ≤
      Real.exp (-(V:ℝ)/1000000) := by
    have hl := competition_leak_scalar V hV 1 (1/8) (13/1080000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [one_mul] at hl
    exact (mul_le_mul_of_nonneg_right hm' (Real.exp_pos _).le).trans hl
  have hlog : 1/5 ≤ 2*Real.log 2-1 := by linarith [Real.log_two_gt_d9]
  have htime : 2/1000000 ≤ (2*Real.log 2-1)*(500+(m:ℝ)+(s:ℝ)) := by
    have hh := mul_le_mul hlog ht (by norm_num : (0:ℝ)≤500) (by linarith : 0 ≤ 2*Real.log 2-1)
    linarith
  have hfood : 2*Real.exp (-(2*Real.log 2-1)*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))) ≤
      Real.exp (-(V:ℝ)/1000000) := by
    have hh := competition_small_prefactor_tail V hV 2
      ((2*Real.log 2-1)*(500+(m:ℝ)+(s:ℝ))) (by norm_num) htime
    simpa only [show -((2*Real.log 2-1)*(500+(m:ℝ)+(s:ℝ)))*(V:ℝ)=
      -(2*Real.log 2-1)*(V:ℝ)*(500+(m:ℝ)+(s:ℝ)) by ring] using hh
  have hfuel : Real.exp (-(V:ℝ)*(500+(m:ℝ)+(s:ℝ))/200) ≤ Real.exp (-(V:ℝ)/1000000) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left ht hv0]
  have hremain : 8*Real.exp (-(V:ℝ)/1000000) ≤ Real.exp (-(2/100000000)*(V:ℝ)) := by
    have hc : (8:ℝ) ≤ Real.exp ((1/1000000-2/100000000)*(V:ℝ)) := by
      linarith [Real.add_one_le_exp ((1/1000000-2/100000000)*(V:ℝ))]
    have hh := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-(V:ℝ)/1000000)).le
    apply hh.trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  unfold competitionTimedRootError competitionTimedOperatingError competitionTimedSupplyError
  linarith

theorem competition_duration_sizing (V : ℕ) (H : ℝ) (hH : 0 < H)
    (hv : Real.log H ≤ (V:ℝ)/1000000) : H ≤ competitionDuration V := by
  rw [← Real.exp_log hH]
  exact Real.exp_le_exp.mpr hv

theorem competition_confidence_sizing (V : ℕ) (rho : ℝ) (hr : 0 < rho)
    (hv : Real.log (2/rho) ≤ (2/100000000)*(V:ℝ)) :
    2*Real.exp (-(2/100000000)*(V:ℝ)) ≤ rho := by
  have hh := Real.exp_le_exp.mpr hv
  rw [Real.exp_log (by positivity : (0:ℝ) < 2/rho)] at hh
  have hp := (div_le_iff₀ hr).mp hh
  rw [show -(2/100000000:ℝ)*(V:ℝ)=-((2/100000000)*(V:ℝ)) by ring,Real.exp_neg]
  change 2 / Real.exp ((2/100000000)*(V:ℝ)) ≤ rho
  exact (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith)

end
end RandomViability.Binding
