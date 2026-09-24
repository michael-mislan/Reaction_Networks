import proofs.FiniteCopyReactor.SwitchedMaterial
import proofs.FiniteCopyReactor.KilledComparison
import proofs.FiniteReservoir.TerminalMaterialProbability
import proofs.FiniteCopyReactor.ThreeClockCutoff
import proofs.FiniteReservoir.JointState

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped NNReal

def ActiveMaterialTail (V M : ℕ) (side : Bool) (sign : ℝ) : Set (BoxState V M) :=
  {X | residenceActive V X.1 ∧ (V:ℝ)/160 ≤ sign*(unitObs side (boxCounts X.1)-(V:ℝ))}

theorem active_material_indicator (V M : ℕ) (side : Bool) (sign : ℝ) (X : BoxState V M) :
    FiniteKernel.eventIndicator (ActiveMaterialTail V M side sign) X=
      if residenceActive V X.1 then FiniteKernel.eventIndicator (TerminalMaterialTail V M side sign) X else 0 := by
  unfold FiniteKernel.eventIndicator ActiveMaterialTail TerminalMaterialTail
  by_cases h : residenceActive V X.1
  · simp [h,h.1]
  · simp [h]

theorem switched_material_discrete (V M : ℕ) (side : Bool) (sign : ℝ) (p : Parameters M)
    (hV : 0 < (V:ℝ)) (hsign : |sign|=1)  (n m k : ℕ) (hn : 11700*V ≤ n+m+k) (N : BoxState V M)
    (hprep : |unitObs side (boxCounts N.1)-(V:ℝ)| ≤ (V:ℝ)/25) :
    (materialKernel V M p hV).steps n
      ((residenceKernel V M p hV).steps m
        ((residenceKernel V M p hV).steps k
          (FiniteKernel.eventIndicator (ActiveMaterialTail V M side sign)))) N ≤ Real.exp (-(V:ℝ)/320000) := by
  let P := materialKernel V M p hV
  let Q := residenceKernel V M p hV
  have h := three_phase_killed_comparison P Q (fun X : BoxState V M => residenceActive V X.1)
    (residence_step_eq V M p hV)
    (FiniteKernel.eventIndicator (TerminalMaterialTail V M side sign))
    (fun X => (FiniteKernel.eventIndicator_bounds _ X).1) n m k N
  have he : FiniteKernel.eventIndicator (ActiveMaterialTail V M side sign)=
      (fun X => if residenceActive V X.1 then FiniteKernel.eventIndicator (TerminalMaterialTail V M side sign) X else 0) :=
    funext (active_material_indicator V M side sign)
  rw [he]
  exact h.trans (terminal_material_after_cutoff V M side sign p hV hsign (n+m+k) hn N hprep)

theorem switched_material_tail (V M : ℕ) (side : Bool) (sign : ℝ) (p : Parameters M)
    (hV : 0 < (V:ℝ)) (hsign : |sign|=1)  (N : BoxState V M)
    (hprep : |unitObs side (boxCounts N.1)-(V:ℝ)| ≤ (V:ℝ)/25) :
    switchedState V M p hV
      (FiniteKernel.eventIndicator (ActiveMaterialTail V M side sign)) N ≤
      Real.exp (-(V:ℝ)/320000)+Real.exp (-(V:ℝ)) := by
  have h := finite_three_clock_cutoff (materialKernel V M p hV)
    (residenceKernel V M p hV) (residenceKernel V M p hV)
    ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V)
    (FiniteKernel.eventIndicator (ActiveMaterialTail V M side sign)) (FiniteKernel.eventIndicator_bounds _)
    (11700*V) (Real.exp (-(V:ℝ)/320000)) (99/100) (Real.exp_pos _).le (by norm_num) (by norm_num) N
    (fun n m k hn => switched_material_discrete V M side sign p hV hsign n m k hn N hprep)
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
