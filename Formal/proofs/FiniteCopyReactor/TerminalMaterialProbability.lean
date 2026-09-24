import proofs.FiniteCopyReactor.TerminalMaterialSteps
import proofs.RandomViability.BindingPoissonDeadline

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators NNReal

theorem material_clock_contraction (V : ℕ) (hV : 0 < (V:ℝ)) (n : ℕ) (hn : 11700*V ≤ n) :
    0 ≤ (1-1/(3000*(V:ℝ)))^n ∧ (1-1/(3000*(V:ℝ)))^n ≤ 1/40 := by
  have hv1 : (1:ℝ) ≤ V := by
    have hv : 0 < V := by exact_mod_cast hV
    exact_mod_cast (show 1 ≤ V by omega)
  have hq : 0 < 3000*(V:ℝ) := by positivity
  have hq1 : 1 ≤ 3000*(V:ℝ) := by linarith
  have ha : 0 ≤ 1-1/(3000*(V:ℝ)) := sub_nonneg.mpr ((div_le_one hq).mpr hq1)
  refine ⟨pow_nonneg ha _,?_⟩
  have he : 1-1/(3000*(V:ℝ)) ≤ Real.exp (-(1/(3000*(V:ℝ)))) := by
    linarith [Real.add_one_le_exp (-(1/(3000*(V:ℝ))))]
  have hp := pow_le_pow_left₀ ha he n
  rw [← Real.exp_nat_mul] at hp
  have hn' : (11700:ℝ)*V ≤ n := by exact_mod_cast hn
  have htime : (39/10:ℝ) ≤ (n:ℝ)/(3000*(V:ℝ)) := (le_div_iff₀ hq).mpr (by nlinarith)
  have hs := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 39/10 by norm_num) 8
  norm_num [Finset.sum_range_succ] at hs
  have h40 : (40:ℝ) ≤ Real.exp (39/10) := by linarith
  have hneg : Real.exp (-(39/10:ℝ)) ≤ 1/40 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<40) h40
  apply hp.trans
  apply le_trans _ hneg
  apply Real.exp_le_exp.mpr
  rw [show (n:ℝ)*(-(1/(3000*(V:ℝ)))) = -(n:ℝ)/(3000*(V:ℝ)) by ring]
  simpa only [neg_div] using neg_le_neg htime

def TerminalMaterialTail (V : ℕ) (side : Bool) (sign : ℝ) : Set (BoxCounts V) :=
  {X | resourceGood (boxCounts X) V ∧ (V:ℝ)/160 ≤ sign*(unitObs side (boxCounts X)-(V:ℝ))}

theorem terminal_material_indicator (V : ℕ) (side : Bool) (sign : ℝ) (X : BoxCounts V) :
    FiniteKernel.eventIndicator (TerminalMaterialTail V side sign) X ≤
      Real.exp (-(V:ℝ)/160000)*materialTest V side (sign/1000) X := by
  by_cases h : X ∈ TerminalMaterialTail V side sign
  · rw [FiniteKernel.eventIndicator,if_pos h]
    simp only [materialTest,if_pos h.1]
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    linarith [h.2]
  · rw [FiniteKernel.eventIndicator,if_neg h]
    unfold materialTest
    split_ifs <;> positivity

theorem terminal_material_after_cutoff (V : ℕ) (side : Bool) (sign r d : ℝ)
    (hV : 0 < (V:ℝ)) (hsign : |sign|=1) (hr : 0 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (n : ℕ) (hn : 11700*V ≤ n) (N : BoxCounts V)
    (hprep : |unitObs side (boxCounts N)-(V:ℝ)| ≤ (V:ℝ)/25) :
    (materialKernel V r d hV hr hr' hd hd').steps n
      (FiniteKernel.eventIndicator (TerminalMaterialTail V side sign)) N ≤ Real.exp (-(V:ℝ)/320000) := by
  let P := materialKernel V r d hV hr hr' hd hd'
  have hv1 : (1:ℝ) ≤ V := by
    have hv : 0 < V := by exact_mod_cast hV
    exact_mod_cast (show 1 ≤ V by omega)
  have hq : 0 < 3000*(V:ℝ) := by positivity
  have hq1 : 1 ≤ 3000*(V:ℝ) := by linarith
  have hs : |sign/1000| ≤ 1/100 := by rw [abs_div,hsign]; norm_num
  have hss : (sign/1000)^2=1/1000000 := by
    have hh : sign^2=1 := by nlinarith [sq_abs sign]
    nlinarith
  have hi := P.steps_mono (terminal_material_indicator V side sign) n N
  rw [P.steps_scale] at hi
  have ht := material_test_steps V side r d (sign/1000) (3000*(V:ℝ)) hV hr hd hs hq hq1
    (material_total_bound V r d hV hr hr' hd hd') n N
  have hpar : |(1-1/(3000*(V:ℝ)))^n*(sign/1000)| ≤ 1/40000 := by
    rw [abs_mul,abs_of_nonneg (material_clock_contraction V hV n hn).1,abs_div,hsign]
    norm_num only [abs_of_pos (show (0:ℝ) < 1000 by norm_num)]
    nlinarith [(material_clock_contraction V hV n hn).2]
  have hinit : materialTest V side ((1-1/(3000*(V:ℝ)))^n*(sign/1000)) N ≤
      Real.exp ((V:ℝ)/1000000) := by
    unfold materialTest
    split_ifs
    · apply Real.exp_le_exp.mpr
      have hm := mul_le_mul hpar hprep (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/40000)
      have hab := le_abs_self (((1-1/(3000*(V:ℝ)))^n*(sign/1000))*(unitObs side (boxCounts N)-(V:ℝ)))
      rw [abs_mul] at hab
      nlinarith
    · exact (Real.exp_pos _).le
  have hh := hi.trans (mul_le_mul_of_nonneg_left (ht.trans
    (mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le)) (Real.exp_pos _).le)
  rw [hss,← mul_assoc,← Real.exp_add,← Real.exp_add] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  linarith

theorem terminal_material_signed_probability (V : ℕ) (side : Bool) (sign r d : ℝ)
    (hV : 0 < (V:ℝ)) (hsign : |sign|=1) (hr : 0 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (hprep : |unitObs side (boxCounts N)-(V:ℝ)| ≤ (V:ℝ)/25) :
    (materialKernel V r d hV hr hr' hd hd').poissonized ((12000:ℝ≥0)*V)
      (FiniteKernel.eventIndicator (TerminalMaterialTail V side sign)) N ≤
        Real.exp (-(V:ℝ)/320000)+Real.exp (-(V:ℝ)) := by
  have h := poissonized_after_cutoff (materialKernel V r d hV hr hr' hd hd')
    (TerminalMaterialTail V side sign) N ((12000:ℝ≥0)*V) (11700*V)
    (Real.exp (-(V:ℝ)/320000)) (99/100) (Real.exp_pos _).le (by norm_num) (by norm_num)
    (fun n hn => terminal_material_after_cutoff V side sign r d hV hsign hr hr' hd hd' n hn N hprep)
  apply h.trans
  apply add_le_add le_rfl
  apply Real.exp_le_exp.mpr
  have hl := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<99/100 by norm_num)
  norm_num at hl
  have hm := mul_le_mul_of_nonneg_left hl hV.le
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat]
  nlinarith

end
end FiniteCopyReactor

