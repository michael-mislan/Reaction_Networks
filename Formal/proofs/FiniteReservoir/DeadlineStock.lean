import proofs.FiniteReservoir.EntryResidence

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal
open FiniteCopyReactor (clampedResidence clamped_residence_bounds clamped_residence_high stopped_poisson_comparison materialExitError)

def deadlineStockError (V : ℝ) : ℝ :=
  Real.exp (-(3/5000000)*V)+Real.exp (-V/2)+materialExitError V+
    Real.exp (-V/10000)+8250*V*Real.exp (-V/10000+9/500)

theorem actual_deadline_stock (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (N : BoxState V M)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N.1))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N.1) ∧
      unitObs side (boxCounts N.1) ≤ (51/50)*(V:ℝ)) :
    (materialKernel V M p hV).poissonized ((8250:ℝ≥0)*V)
      (fun X => clampedResidence V (boxCounts X.1)) N ≤ deadlineStockError V := by
  let P := materialKernel V M p hV
  let Q := entryKernel V M p hV
  let A : Set (BoxState V M) := {X | entryActive V ((3/50)*(V:ℝ)) X.1}
  let B : Set (BoxState V M) := {X | ¬resourceGood (boxCounts X.1) V}
  let F := fun X : BoxState V M => clampedResidence V (boxCounts X.1)
  let c := Real.exp (-(V:ℝ)/10000)
  have hi (X) : F X ≤ FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X+c := by
    by_cases ha : X ∈ A
    · rw [FiniteKernel.eventIndicator,if_pos ha]
      have hb : 0 ≤ FiniteKernel.eventIndicator B X := by
        unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num
      have hh := (clamped_residence_bounds V (boxCounts X.1)).2
      dsimp [F,c] at *
      linarith [Real.exp_pos (-(V:ℝ)/10000)]
    · by_cases hb : X ∈ B
      · simp only [FiniteKernel.eventIndicator,if_neg ha,if_pos hb,zero_add]
        exact (clamped_residence_bounds V (boxCounts X.1)).2.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
      · simp only [FiniteKernel.eventIndicator,if_neg ha,if_neg hb,zero_add]
        apply clamped_residence_high
        have hc : resourceGood (boxCounts X.1) V := not_not.mp hb
        have hnh : ¬weightedCount (boxCounts X.1)<(3/50)*(V:ℝ) := fun hy => ha ⟨hc,hy⟩
        exact le_of_not_gt hnh
  have hn (E : Set (BoxState V M)) (X) : 0 ≤ FiniteKernel.eventIndicator E X := by
    unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num
  have hh := Q.poissonized_mono ((8250:ℝ≥0)*V) F _
    (fun X => (clamped_residence_bounds V (boxCounts X.1)).1)
    (fun X => add_nonneg (add_nonneg (hn A X) (hn B X)) (Real.exp_pos _).le) hi N
  rw [Q.poissonized_add _ _ _ (fun X => add_nonneg (hn A X) (hn B X)) (fun _ => (Real.exp_pos _).le),
    Q.poissonized_add _ _ _ (hn A) (hn B),Q.poissonized_const] at hh
  have hc := stopped_poisson_comparison P Q (fun X => entryActive V ((3/50)*(V:ℝ)) X.1)
    (routine_entry_step V M p hV) F
    (fun X => (clamped_residence_bounds V (boxCounts X.1)).1)
    (Real.exp (-(V:ℝ)/10000+9/500)) (Real.exp_pos _).le
    (material_clamped_step V M p hV) ((8250:ℝ≥0)*V) N
  have he := seeded_recovery_deadline V M p hV N hstock
  have hm := entry_material_exit V M p hV N hprep
  have hrhs := hc.trans (add_le_add hh le_rfl)
  norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] at hrhs
  dsimp [A,B,c,Q,F,P] at *
  unfold deadlineStockError
  linarith

end
end FiniteReservoir
