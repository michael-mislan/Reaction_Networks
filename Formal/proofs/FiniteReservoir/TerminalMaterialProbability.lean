import proofs.FiniteReservoir.TerminalMaterialSteps
import proofs.FiniteCopyReactor.TerminalMaterialProbability
import proofs.RandomViability.BindingPoissonDeadline

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators NNReal

def TerminalMaterialTail (V M : ℕ) (side : Bool) (sign : ℝ) : Set (BoxState V M) :=
  {X | resourceGood (boxCounts X.1) V ∧ (V:ℝ)/160 ≤ sign*(unitObs side (boxCounts X.1)-(V:ℝ))}

theorem terminal_material_indicator (V M : ℕ) (side : Bool) (sign : ℝ) (X : BoxState V M) :
    FiniteKernel.eventIndicator (TerminalMaterialTail V M side sign) X ≤
      Real.exp (-(V:ℝ)/160000)*materialTest V M side (sign/1000) X := by
  by_cases h : X ∈ TerminalMaterialTail V M side sign
  · rw [FiniteKernel.eventIndicator,if_pos h]
    simp only [materialTest,if_pos h.1]
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    linarith [h.2]
  · rw [FiniteKernel.eventIndicator,if_neg h]
    unfold materialTest
    split_ifs <;> positivity

theorem terminal_material_after_cutoff (V M : ℕ) (side : Bool) (sign : ℝ) (p : Parameters M)
    (hV : 0 < (V:ℝ)) (hsign : |sign|=1) (n : ℕ) (hn : 11700*V ≤ n) (N : BoxState V M)
    (hprep : |unitObs side (boxCounts N.1)-(V:ℝ)| ≤ (V:ℝ)/25) :
    (materialKernel V M p hV).steps n
      (FiniteKernel.eventIndicator (TerminalMaterialTail V M side sign)) N ≤ Real.exp (-(V:ℝ)/320000) := by
  let P := materialKernel V M p hV
  have hv1 : (1:ℝ) ≤ V := by
    have hv : 0 < V := by exact_mod_cast hV
    exact_mod_cast (show 1 ≤ V by omega)
  have hq : 0 < 3000*(V:ℝ) := by positivity
  have hq1 : 1 ≤ 3000*(V:ℝ) := by linarith
  have hs : |sign/1000| ≤ 1/100 := by rw [abs_div,hsign]; norm_num
  have hss : (sign/1000)^2=1/1000000 := by
    have hh : sign^2=1 := by nlinarith [sq_abs sign]
    nlinarith
  have hi := P.steps_mono (terminal_material_indicator V M side sign) n N
  rw [P.steps_scale] at hi
  have ht := material_test_steps V M side p (sign/1000) (3000*(V:ℝ)) hV hs hq hq1
    (material_total V M p hV) n N
  have hpar : |(1-1/(3000*(V:ℝ)))^n*(sign/1000)| ≤ 1/40000 := by
    rw [abs_mul,abs_of_nonneg (FiniteCopyReactor.material_clock_contraction V hV n hn).1,abs_div,hsign]
    norm_num only [abs_of_pos (show (0:ℝ) < 1000 by norm_num)]
    nlinarith [(FiniteCopyReactor.material_clock_contraction V hV n hn).2]
  have hinit : materialTest V M side ((1-1/(3000*(V:ℝ)))^n*(sign/1000)) N ≤
      Real.exp ((V:ℝ)/1000000) := by
    unfold materialTest
    split_ifs
    · apply Real.exp_le_exp.mpr
      have hm := mul_le_mul hpar hprep (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/40000)
      have hab := le_abs_self (((1-1/(3000*(V:ℝ)))^n*(sign/1000))*(unitObs side (boxCounts N.1)-(V:ℝ)))
      rw [abs_mul] at hab
      nlinarith
    · exact (Real.exp_pos _).le
  have hh := hi.trans (mul_le_mul_of_nonneg_left (ht.trans
    (mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le)) (Real.exp_pos _).le)
  rw [hss,← mul_assoc,← Real.exp_add,← Real.exp_add] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  linarith

theorem terminal_material_signed_probability (V M : ℕ) (side : Bool) (sign : ℝ) (p : Parameters M)
    (hV : 0 < (V:ℝ)) (hsign : |sign|=1) (N : BoxState V M)
    (hprep : |unitObs side (boxCounts N.1)-(V:ℝ)| ≤ (V:ℝ)/25) :
    (materialKernel V M p hV).poissonized ((12000:ℝ≥0)*V)
      (FiniteKernel.eventIndicator (TerminalMaterialTail V M side sign)) N ≤
        Real.exp (-(V:ℝ)/320000)+Real.exp (-(V:ℝ)) := by
  have h := poissonized_after_cutoff (materialKernel V M p hV)
    (TerminalMaterialTail V M side sign) N ((12000:ℝ≥0)*V) (11700*V)
    (Real.exp (-(V:ℝ)/320000)) (99/100) (Real.exp_pos _).le (by norm_num) (by norm_num)
    (fun n hn => terminal_material_after_cutoff V M side sign p hV hsign n hn N hprep)
  apply h.trans
  apply add_le_add le_rfl
  apply Real.exp_le_exp.mpr
  have hl := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<99/100 by norm_num)
  norm_num at hl
  have hm := mul_le_mul_of_nonneg_left hl hV.le
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat]
  nlinarith

end
end FiniteReservoir

