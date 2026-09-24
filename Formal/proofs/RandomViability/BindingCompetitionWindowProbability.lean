import proofs.RandomViability.BindingCompetitionWindowModel
import proofs.FiniteCopy.KernelExpectations

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal
variable {V C : ℕ}

def competitionWindowActive (X : CompetitionWindowState V C) : Prop :=
  competitionEnabled X.1 ∧ competitionPhase X.1=1 ∧ X.2.val<C

def competitionWindowTest (X : CompetitionWindowState V C) : ℝ := if competitionWindowActive X then Real.exp (-(X.2.val:ℝ)/8) else 0

theorem competitionWindowTest_nonneg (X : CompetitionWindowState V C) : 0 ≤ competitionWindowTest X := by
  unfold competitionWindowTest
  split_ifs <;> positivity

theorem competitionWindowTest_le_one (X : CompetitionWindowState V C) : competitionWindowTest X ≤ 1 := by
  unfold competitionWindowTest
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    have h := Nat.cast_nonneg (α := ℝ) X.2.val
    linarith
  · norm_num

theorem competitionWindowTest_next_bound (X : CompetitionWindowState V C) (j : CompetitionChannel) :
    competitionWindowTest (competitionWindowNext X j) ≤ Real.exp (-(X.2.val:ℝ)/8)*Real.exp (-(competitionExportUnits j:ℝ)/8) := by
  unfold competitionWindowTest
  split_ifs with h
  · have hc := h.2.2
    change min C (X.2.val+competitionExportUnits j)<C at hc
    have hm : X.2.val+competitionExportUnits j ≤ C := by omega
    change Real.exp (-((min C (X.2.val+competitionExportUnits j):ℕ):ℝ)/8) ≤ _
    rw [Nat.min_eq_right hm,Nat.cast_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    apply le_of_eq
    ring
  · positivity

theorem competition_window_inactive_generator (eps k r delta : ℝ) (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (X : CompetitionWindowState V C) (h : ¬competitionWindowActive X) :
    (competitionWindowModel V C eps k r delta hV heps hk hr hd).generator competitionWindowTest X=0 := by
  by_cases hen : competitionEnabled X.1
  · by_cases hp : competitionPhase X.1=0
    · exact competition_window_deadline_failure V C eps k r delta hV heps hk hr hd competitionWindowTest X hp
    · have hp1 : competitionPhase X.1=1 := by have hh := hen.1; omega
      have hc : X.2.val=C := by
        have hlt := X.2.isLt
        have hh : ¬X.2.val<C := fun hh => h ⟨hen,hp1,hh⟩
        omega
      have hn (j : CompetitionChannel) : competitionWindowTest (competitionWindowNext X j)=0 := by
        unfold competitionWindowTest
        split_ifs with hnext
        · have hh := hnext.2.2
          change min C (X.2.val+competitionExportUnits j)<C at hh
          omega
        · rfl
      simp only [FiniteJumpModel.generator,competitionWindowModel]
      simp only [hn]
      simp [competitionWindowTest,h]
  · simp [FiniteJumpModel.generator,competitionWindowModel,competitionModel,hen]

theorem competition_window_generator_decay (eps k r delta : ℝ) (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (X : CompetitionWindowState V C) :
    (competitionWindowModel V C eps k r delta hV heps hk hr hd).generator competitionWindowTest X ≤ -((V:ℝ)/27000)*competitionWindowTest X := by
  by_cases h : competitionWindowActive X
  · have hp0 : competitionPhase X.1≠0 := by have hh := h.2.1; omega
    have hY : (V:ℝ)/5000 ≤ weightedCount (boxCounts (competitionCounts X.1)) := X.1.property.2.1 h.2.1
    have hg := competition_export_tilt_floor (boxCounts (competitionCounts X.1)) V eps k r delta hY
    calc
      _ ≤ Real.exp (-(X.2.val:ℝ)/8)*
          (∑ j,competitionRate (boxCounts (competitionCounts X.1)) V eps k r delta j*
            (Real.exp (-(competitionExportUnits j:ℝ)/8)-1)) := by
        simp only [FiniteJumpModel.generator,competitionWindowModel,if_neg hp0,competitionModel,if_pos h.1,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        have hn := competitionWindowTest_next_bound X j
        have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right hn (competitionWindowTest X))
          (competitionRate_nonneg (boxCounts (competitionCounts X.1)) V eps k r delta hV heps hk hr hd j)
        have hcurr : competitionWindowTest X=Real.exp (-(X.2.val:ℝ)/8) := by simp [competitionWindowTest,h]
        rw [hcurr] at hh ⊢
        convert hh using 1
        ring
      _ ≤ Real.exp (-(X.2.val:ℝ)/8)*(-(V:ℝ)/27000) :=
        mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
      _ = _ := by rw [competitionWindowTest,if_pos h]; ring
  · rw [competition_window_inactive_generator eps k r delta hV heps hk hr hd X h]
    simp [competitionWindowTest,h]

theorem competition_window_indicator_bound (X : CompetitionWindowState V C) :
    FiniteKernel.eventIndicator {X | competitionWindowActive X} X ≤ Real.exp ((C:ℝ)/8)*competitionWindowTest X := by
  by_cases h : competitionWindowActive X
  · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_pos h,competitionWindowTest]
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have hc : (X.2.val:ℝ) ≤ C := by exact_mod_cast h.2.2.le
    linarith
  · simp [FiniteKernel.eventIndicator,competitionWindowTest,h]


theorem competition_window_probability (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q t : ℝ≥0) (hq : 0 < (q:ℝ))
    (hclock : (V:ℝ)/27000 ≤ q)
    (hb : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk hr hd).total X ≤ q)
    (X : CompetitionWindowState V C) :
    ((competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hb).poissonized (q*t)
      (FiniteKernel.eventIndicator {Z | competitionWindowActive Z}) X ≤
      Real.exp ((C:ℝ)/8-(t:ℝ)*(V:ℝ)/27000) := by
  let P := (competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hb
  have hdec := (competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformized_decay_bound
    q t hq hb competitionWindowTest competitionWindowTest_nonneg ((V:ℝ)/27000) hclock
    (competition_window_generator_decay eps k r delta hV heps hk hr hd) X
  have hi := P.poissonized_mono (q*t)
    (FiniteKernel.eventIndicator {Z | competitionWindowActive Z})
    (fun Z => Real.exp ((C:ℝ)/8)*competitionWindowTest Z)
    (by intro Z; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (fun Z => mul_nonneg (Real.exp_pos _).le (competitionWindowTest_nonneg Z))
    competition_window_indicator_bound X
  rw [P.poissonized_scale] at hi
  have ht := mul_le_mul_of_nonneg_left (competitionWindowTest_le_one X)
    (Real.exp_pos (-((V:ℝ)/27000)*(t:ℝ))).le
  have hh := hdec.trans (by simpa only [mul_one] using ht)
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos ((C:ℝ)/8)).le
  have he : Real.exp ((C:ℝ)/8)*Real.exp (-((V:ℝ)/27000)*(t:ℝ)) =
      Real.exp ((C:ℝ)/8-(t:ℝ)*(V:ℝ)/27000) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hm
  exact hi.trans hm

end
end RandomViability.Binding
