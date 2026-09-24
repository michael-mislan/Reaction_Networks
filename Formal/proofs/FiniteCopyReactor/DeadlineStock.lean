import proofs.FiniteCopyReactor.EntryResidence

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

def deadlineStockError (V : ℝ) : ℝ :=
  Real.exp (-(3/5000000)*V)+Real.exp (-V/2)+materialExitError V+
    Real.exp (-V/10000)+8250*V*Real.exp (-V/10000+9/500)

theorem actual_deadline_stock (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N) ∧
      unitObs side (boxCounts N) ≤ (51/50)*(V:ℝ)) :
    (materialKernel V r d hV (by linarith) hr' hd hd').poissonized ((8250:ℝ≥0)*V)
      (fun X => clampedResidence V (boxCounts X)) N ≤ deadlineStockError V := by
  let P := materialKernel V r d hV (by linarith) hr' hd hd'
  let Q := routineEntryKernel V r d hV hr hr' hd hd'
  let A : Set (BoxCounts V) := {X | entryActive V ((3/50)*(V:ℝ)) X}
  let B : Set (BoxCounts V) := {X | ¬resourceGood (boxCounts X) V}
  let F := fun X : BoxCounts V => clampedResidence V (boxCounts X)
  let c := Real.exp (-(V:ℝ)/10000)
  have hi (X) : F X ≤ FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X+c := by
    by_cases ha : X ∈ A
    · rw [FiniteKernel.eventIndicator,if_pos ha]
      have hb : 0 ≤ FiniteKernel.eventIndicator B X := by
        unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num
      have hh := (clamped_residence_bounds V (boxCounts X)).2
      dsimp [F,c] at *
      linarith [Real.exp_pos (-(V:ℝ)/10000)]
    · by_cases hb : X ∈ B
      · simp only [FiniteKernel.eventIndicator,if_neg ha,if_pos hb,zero_add]
        exact (clamped_residence_bounds V (boxCounts X)).2.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
      · simp only [FiniteKernel.eventIndicator,if_neg ha,if_neg hb,zero_add]
        apply clamped_residence_high
        have hc : resourceGood (boxCounts X) V := not_not.mp hb
        have hnh : ¬weightedCount (boxCounts X)<(3/50)*(V:ℝ) := fun hy => ha ⟨hc,hy⟩
        exact le_of_not_gt hnh
  have hn (E : Set (BoxCounts V)) (X) : 0 ≤ FiniteKernel.eventIndicator E X := by
    unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num
  have hh := Q.poissonized_mono ((8250:ℝ≥0)*V) F _
    (fun X => (clamped_residence_bounds V (boxCounts X)).1)
    (fun X => add_nonneg (add_nonneg (hn A X) (hn B X)) (Real.exp_pos _).le) hi N
  rw [Q.poissonized_add _ _ _ (fun X => add_nonneg (hn A X) (hn B X)) (fun _ => (Real.exp_pos _).le),
    Q.poissonized_add _ _ _ (hn A) (hn B),Q.poissonized_const] at hh
  have hc := stopped_poisson_comparison P Q (entryActive V ((3/50)*(V:ℝ)))
    (routine_entry_step V r d hV hr hr' hd hd') F
    (fun X => (clamped_residence_bounds V (boxCounts X)).1)
    (Real.exp (-(V:ℝ)/10000+9/500)) (Real.exp_pos _).le
    (material_clamped_step V r d hV hr hr' hd hd') ((8250:ℝ≥0)*V) N
  have he := seeded_recovery_deadline V r d hV hr hr' hd hd' N hstock
  have hm := entry_material_exit V r d hV hr hr' hd hd' N hprep
  have hrhs := hc.trans (add_le_add hh le_rfl)
  norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] at hrhs
  dsimp [A,B,c,Q,F,P] at *
  unfold deadlineStockError
  linarith

end
end FiniteCopyReactor
