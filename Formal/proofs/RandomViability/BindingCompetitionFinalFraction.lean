import proofs.RandomViability.BindingCompetitionOperatingWindows

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal
variable {V C : ℕ}

def competitionFinalFailure (P : FiniteKernel (CompetitionWindowState V C))
    (q s : ℝ≥0) (X : CompetitionMonitorState V C) : ℝ :=
  P.poissonized (q*s) (fun Y => competitionOperatingFailure (Y,X.2)) X.1

theorem competition_window_source_time (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q s : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk hr hd).total X ≤ q)
    (f : CompetitionCounts V → ℝ) (hf : ∀ X, 0 ≤ f X) (b : ℝ) (hb : 0 ≤ b)
    (hgen : ∀ X, (competitionModel V eps k r delta hV heps hk hr hd).generator f X ≤ b)
    (X : CompetitionWindowState V C) :
    ((competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hbound).poissonized (q*s)
      (fun Z => f Z.1) X ≤ f X.1+(s:ℝ)*b := by
  let M := competitionWindowModel V C eps k r delta hV heps hk hr hd
  have hg (Y : CompetitionWindowState V C) : M.generator (fun Z => f Z.1) Y ≤ b := by
    by_cases hp : competitionPhase Y.1=0
    · rw [competition_window_deadline_failure V C eps k r delta hV heps hk hr hd _ Y hp]
      exact hb
    · rw [competition_window_project V C eps k r delta hV heps hk hr hd f Y hp]
      exact hgen Y.1
  have hh := (M.uniformize q hq hbound).poissonized_drift_bound (q*s) (fun Z => f Z.1) (b/(q:ℝ))
    (fun Z => hf _) (M.uniformize_drift q hq hbound _ b hg) X
  have he : ((q*s:ℝ≥0):ℝ)*(b/(q:ℝ))=(s:ℝ)*b := by rw [NNReal.coe_mul]; field_simp
  simpa only [he] using hh

/-- No new completed window is assessed in the final fractional interval. -/
theorem competition_fraction_bad (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q s : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk hr hd).total X ≤ q)
    (X : CompetitionMonitorState V C) :
    ((competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hbound).poissonized (q*s)
      (fun Z => competitionMonitorBad (Z,X.2)) X.1 ≤ competitionMonitorBad X := by
  let P := (competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hbound
  let f : CompetitionWindowState V C → ℝ := fun Z => competitionMonitorBad (Z,X.2)
  have hf (Z) : 0 ≤ f Z := competitionMonitorBad_nonneg _
  have hstep (Z : CompetitionWindowState V C) : P.step f Z ≤ 1*f Z := by
    by_cases hg : competitionWindowGood Z
    · cases hp : X.2 with
      | true =>
        have he : f=(fun _ => 0) := by funext Y; simp [f,competitionMonitorBad,FiniteKernel.eventIndicator,hp]
        simp [he,P.step_const]
      | false =>
        have he : f Z=1 := by simp [f,competitionMonitorBad,FiniteKernel.eventIndicator,hg,hp]
        have hh : ∀ Y, f Y ≤ 1 := by
          intro Y
          unfold f competitionMonitorBad FiniteKernel.eventIndicator
          split_ifs <;> norm_num
        have hm := P.step_mono hh Z
        simpa only [P.step_const,he,one_mul] using hm
    · rw [competition_window_bad_step eps k r delta hV heps hk hr hd q hq hbound Z hg]
      simp
  have hh := P.poissonized_decay_bound (q*s) f hf 1 (by norm_num) hstep X.1
  simpa only [sub_self,mul_zero,Real.exp_zero,one_mul] using hh

theorem competition_final_fraction_bound (V C : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5)
    (q s : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk (by linarith) hd).total X ≤ q)
    (X : CompetitionMonitorState V C) :
    competitionFinalFailure
      ((competitionWindowModel V C eps k r delta hV heps hk (by linarith) hd).uniformize q hq hbound) q s X ≤
      competitionNoEntry X.1.1+resourcePotential V (boxCounts (competitionCounts X.1.1))+
      competitionTrackedReturnPotential X.1.1+competitionMonitorBad X+
      (s:ℝ)*(4*resourceSource V+competitionReturnSource V) := by
  let P := (competitionWindowModel V C eps k r delta hV heps hk (by linarith) hd).uniformize q hq hbound
  let f : CompetitionWindowState V C → ℝ := fun Z => competitionNoEntry Z.1
  let g : CompetitionWindowState V C → ℝ := fun Z => resourcePotential V (boxCounts (competitionCounts Z.1))
  let h : CompetitionWindowState V C → ℝ := fun Z => competitionTrackedReturnPotential Z.1
  let j : CompetitionWindowState V C → ℝ := fun Z => competitionMonitorBad (Z,X.2)
  have hf (Z) : 0 ≤ f Z := competition_noentry_nonneg _
  have hg (Z) : 0 ≤ g Z := resourcePotential_nonneg V _
  have hh (Z) : 0 ≤ h Z := competition_tracked_return_nonneg _
  have hj (Z) : 0 ≤ j Z := competitionMonitorBad_nonneg _
  have hfg (Z) : 0 ≤ f Z+g Z := add_nonneg (hf Z) (hg Z)
  have hfgh (Z) : 0 ≤ f Z+g Z+h Z := add_nonneg (hfg Z) (hh Z)
  have ho (Z : CompetitionWindowState V C) : 0 ≤ competitionOperatingFailure (Z,X.2) := by
    unfold competitionOperatingFailure FiniteKernel.eventIndicator
    split_ifs <;> norm_num
  have hm := P.poissonized_mono (q*s) _ (fun Z => f Z+g Z+h Z+j Z) ho
    (fun Z => add_nonneg (hfgh Z) (hj Z)) (fun Z => competition_failure_decomposition (Z,X.2)) X.1
  rw [P.poissonized_add _ _ _ hfgh hj,P.poissonized_add _ _ _ hfg hh,P.poissonized_add _ f g hf hg] at hm
  have hn := competition_window_source_time eps k r delta hV heps hk (by linarith) hd q s hq hbound
    competitionNoEntry competition_noentry_nonneg 0 le_rfl
    (competition_noentry_generator eps k r delta hV heps hk (by linarith) hd) X.1
  have hrb := competition_window_source_time eps k r delta hV heps hk (by linarith) hd q s hq hbound
    _ (fun Z => resourcePotential_nonneg V _) _ (by unfold resourceSource; positivity)
    (competition_resource_foster V eps k r delta hV heps (by linarith) hk hk1 (by linarith) hr1 hd) X.1
  have hrt := competition_window_source_time eps k r delta hV heps hk (by linarith) hd q s hq hbound
    _ competition_tracked_return_nonneg _ (by unfold competitionReturnSource; positivity)
    (competition_tracked_return_foster V eps k r delta hV heps heps1 hk hk1 hr hr1 hd hd1) X.1
  have hjb := competition_fraction_bad eps k r delta hV heps hk (by linarith) hd q s hq hbound X
  change P.poissonized (q*s) f X.1 ≤ _ at hn
  change P.poissonized (q*s) g X.1 ≤ _ at hrb
  change P.poissonized (q*s) h X.1 ≤ _ at hrt
  change P.poissonized (q*s) j X.1 ≤ _ at hjb
  change P.poissonized (q*s) (fun Z => competitionOperatingFailure (Z,X.2)) X.1 ≤ _
  dsimp [f,g,h,j] at hm hn hrb hrt hjb
  linarith

end
end RandomViability.Binding
