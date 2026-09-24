import proofs.RandomViability.BindingCompetitionEntryLaw
import proofs.RandomViability.BindingCompetitionTrackedReturn
import proofs.RandomViability.BindingExportTilt

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

abbrev CompetitionWindowState (V C : ℕ) := CompetitionCounts V × Fin (C+1)

def competitionExportUnits : CompetitionChannel → ℕ
  | .inl j => exportUnits j
  | .inr _ => 0

theorem competitionExportUnits_real (j : CompetitionChannel) :
    (competitionExportUnits j:ℝ) = competitionExport j := by
  cases j with
  | inl j => exact exportUnits_real j
  | inr j => simp [competitionExportUnits,competitionExport]

def competitionWindowNext {V C : ℕ} (X : CompetitionWindowState V C)
    (j : CompetitionChannel) : CompetitionWindowState V C :=
  (competitionTrackedNext X.1 j,⟨min C (X.2.val+competitionExportUnits j),by
    have h := Nat.min_le_left C (X.2.val+competitionExportUnits j)
    omega⟩)

/-- At observation time, histories missing the entry deadline are absorbed.
Reaching the export cap never disables successful chemistry. -/
def competitionWindowModel (V C : ℕ) (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta) :
    FiniteJumpModel (CompetitionWindowState V C) CompetitionChannel where
  next := competitionWindowNext
  rate X j := if competitionPhase X.1=0 then 0
    else (competitionModel V eps k r delta hV heps hk hr hd).rate X.1 j
  nonneg X j := by
    split_ifs
    · rfl
    · exact (competitionModel V eps k r delta hV heps hk hr hd).nonneg X.1 j

theorem competition_window_project (V C : ℕ) (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (f : CompetitionCounts V → ℝ) (X : CompetitionWindowState V C) (h : competitionPhase X.1≠0) :
    (competitionWindowModel V C eps k r delta hV heps hk hr hd).generator (fun Z => f Z.1) X =
      (competitionModel V eps k r delta hV heps hk hr hd).generator f X.1 := by
  simp only [FiniteJumpModel.generator,competitionWindowModel,if_neg h,competitionWindowNext]
  rfl

theorem competition_window_deadline_failure (V C : ℕ) (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (f : CompetitionWindowState V C → ℝ) (X : CompetitionWindowState V C) (h : competitionPhase X.1=0) :
    (competitionWindowModel V C eps k r delta hV heps hk hr hd).generator f X = 0 := by
  simp [FiniteJumpModel.generator,competitionWindowModel,h]

theorem competition_window_total (V C : ℕ) (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr1 : r ≤ 22) (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5)
    (X : CompetitionWindowState V C) :
    (competitionWindowModel V C eps k r delta hV heps hk hr hd).total X ≤ 3000*V := by
  by_cases h : competitionPhase X.1=0
  · simp [FiniteJumpModel.total,competitionWindowModel,h]
  · simpa only [FiniteJumpModel.total,competitionWindowModel,if_neg h] using
      competition_model_total V eps k r delta hV heps heps1 hk hk1 hr hr1 hd hd1 X.1

theorem competition_export_tilt (N : Counts) (V eps k r delta : ℝ) :
    (∑ j,competitionRate N V eps k r delta j *
      (Real.exp (-(competitionExportUnits j:ℝ)/8)-1)) ≤ -(5/27)*weightedCount N := by
  simpa only [Fintype.sum_sum_type,competitionRate,competitionExportUnits,
    Nat.cast_zero,neg_zero,zero_div,Real.exp_zero,sub_self,mul_zero,
    Finset.sum_const_zero,add_zero] using export_tilt_bound N V eps k r

theorem competition_export_tilt_floor (N : Counts) (V eps k r delta : ℝ)
    (h : V/5000 ≤ weightedCount N) :
    (∑ j,competitionRate N V eps k r delta j *
      (Real.exp (-(competitionExportUnits j:ℝ)/8)-1)) ≤ -V/27000 := by
  have hb := competition_export_tilt N V eps k r delta
  linarith

end
end RandomViability.Binding
