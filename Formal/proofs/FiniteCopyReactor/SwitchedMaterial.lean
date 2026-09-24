import proofs.FiniteCopyReactor.KilledComparison
import proofs.FiniteCopyReactor.TerminalMaterialProbability
import proofs.FiniteCopyReactor.ThreeClockCutoff
import proofs.FiniteCopyReactor.JointState

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

theorem three_phase_killed_comparison {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (active : α → Prop) (hQ : ∀ f x, Q.step f x = if active x then P.step f x else f x)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (n m k : ℕ) (x : α) :
    P.steps n (Q.steps m (Q.steps k (fun y => if active y then f y else 0))) x ≤
      P.steps (n+m+k) f x := by
  have h := P.steps_mono (killed_steps_comparison P Q active hQ f hf (m+k)) n x
  rw [show Q.steps (m+k) (fun y => if active y then f y else 0)=
      Q.steps m (Q.steps k (fun y => if active y then f y else 0)) from funext (steps_comp Q m k _),
    show P.steps (m+k) f=P.steps m (P.steps k f) from funext (steps_comp P m k f)] at h
  simpa only [steps_comp] using h

def ActiveMaterialTail (V : ℕ) (side : Bool) (sign : ℝ) : Set (BoxCounts V) :=
  {X | residenceActive V X ∧ (V:ℝ)/160 ≤ sign*(unitObs side (boxCounts X)-(V:ℝ))}

theorem active_material_indicator (V : ℕ) (side : Bool) (sign : ℝ) (X : BoxCounts V) :
    FiniteKernel.eventIndicator (ActiveMaterialTail V side sign) X=
      if residenceActive V X then FiniteKernel.eventIndicator (TerminalMaterialTail V side sign) X else 0 := by
  unfold FiniteKernel.eventIndicator ActiveMaterialTail TerminalMaterialTail
  by_cases h : residenceActive V X
  · simp [h,h.1]
  · simp [h]

theorem switched_material_discrete (V : ℕ) (side : Bool) (sign r d : ℝ)
    (hV : 0 < (V:ℝ)) (hsign : |sign|=1) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (n m k : ℕ) (hn : 11700*V ≤ n+m+k) (N : BoxCounts V)
    (hprep : |unitObs side (boxCounts N)-(V:ℝ)| ≤ (V:ℝ)/25) :
    (materialKernel V r d hV (by linarith) hr' hd hd').steps n
      ((residenceKernel V r d hV (by linarith) hr' hd hd').steps m
        ((residenceKernel V r d hV (by linarith) hr' hd hd').steps k
          (FiniteKernel.eventIndicator (ActiveMaterialTail V side sign)))) N ≤ Real.exp (-(V:ℝ)/320000) := by
  let P := materialKernel V r d hV (by linarith) hr' hd hd'
  let Q := residenceKernel V r d hV (by linarith) hr' hd hd'
  have h := three_phase_killed_comparison P Q (residenceActive V)
    (residence_step_eq V r d hV hr hr' hd hd')
    (FiniteKernel.eventIndicator (TerminalMaterialTail V side sign))
    (fun X => (FiniteKernel.eventIndicator_bounds _ X).1) n m k N
  have he : FiniteKernel.eventIndicator (ActiveMaterialTail V side sign)=
      (fun X => if residenceActive V X then FiniteKernel.eventIndicator (TerminalMaterialTail V side sign) X else 0) :=
    funext (active_material_indicator V side sign)
  rw [he]
  exact h.trans (terminal_material_after_cutoff V side sign r d hV hsign (by linarith) hr' hd hd' (n+m+k) hn N hprep)

theorem switched_material_tail (V : ℕ) (side : Bool) (sign r d : ℝ)
    (hV : 0 < (V:ℝ)) (hsign : |sign|=1) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (hprep : |unitObs side (boxCounts N)-(V:ℝ)| ≤ (V:ℝ)/25) :
    switchedState V r d hV (by linarith) hr' hd hd'
      (FiniteKernel.eventIndicator (ActiveMaterialTail V side sign)) N ≤
      Real.exp (-(V:ℝ)/320000)+Real.exp (-(V:ℝ)) := by
  have h := finite_three_clock_cutoff (materialKernel V r d hV (by linarith) hr' hd hd')
    (residenceKernel V r d hV (by linarith) hr' hd hd') (residenceKernel V r d hV (by linarith) hr' hd hd')
    ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V)
    (FiniteKernel.eventIndicator (ActiveMaterialTail V side sign)) (FiniteKernel.eventIndicator_bounds _)
    (11700*V) (Real.exp (-(V:ℝ)/320000)) (99/100) (Real.exp_pos _).le (by norm_num) (by norm_num) N
    (fun n m k hn => switched_material_discrete V side sign r d hV hsign hr hr' hd hd' n m k hn N hprep)
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
