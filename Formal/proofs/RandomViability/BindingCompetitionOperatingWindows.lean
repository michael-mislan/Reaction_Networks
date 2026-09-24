import proofs.RandomViability.BindingCompetitionMonitorLinear

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

/-- Common failures are charged once; only the output allowance scales by m. -/
theorem competition_operating_windows (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5)
    (q : ℝ≥0) (hq : 0 < (q:ℝ)) (hclock : (V:ℝ)/27000 ≤ q)
    (hbound : ∀ X, (competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk (by linarith) hd).total X ≤ q)
    (m : ℕ) (X : CompetitionWindowState V (competitionWindowCap V)) :
    competitionMonitorSteps
      ((competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk (by linarith) hd).uniformize q hq hbound) q m
      competitionOperatingFailure (X,true) ≤
      competitionNoEntry X.1+resourcePotential V (boxCounts (competitionCounts X.1))+
      competitionTrackedReturnPotential X.1+
      (m:ℝ)*(4*resourceSource V+competitionReturnSource V)+
      (m:ℝ)*Real.exp (1/8-(13/1080000)*(V:ℝ)) := by
  let P := (competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk (by linarith) hd).uniformize q hq hbound
  let f : CompetitionMonitorState V (competitionWindowCap V) → ℝ := fun Z => competitionNoEntry Z.1.1
  let g : CompetitionMonitorState V (competitionWindowCap V) → ℝ := fun Z => resourcePotential V (boxCounts (competitionCounts Z.1.1))
  let h : CompetitionMonitorState V (competitionWindowCap V) → ℝ := fun Z => competitionTrackedReturnPotential Z.1.1
  have hf (Z) : 0 ≤ f Z := competition_noentry_nonneg _
  have hg (Z) : 0 ≤ g Z := resourcePotential_nonneg V _
  have hh (Z) : 0 ≤ h Z := competition_tracked_return_nonneg _
  have hfg (Z) : 0 ≤ f Z+g Z := add_nonneg (hf Z) (hg Z)
  have hfgh (Z) : 0 ≤ f Z+g Z+h Z := add_nonneg (hfg Z) (hh Z)
  have ho (Z : CompetitionMonitorState V (competitionWindowCap V)) : 0 ≤ competitionOperatingFailure Z := by
    unfold competitionOperatingFailure FiniteKernel.eventIndicator
    split_ifs <;> norm_num
  have hm := competition_monitor_steps_mono P q competitionOperatingFailure
    (fun Z => f Z+g Z+h Z+competitionMonitorBad Z) ho
    (fun Z => add_nonneg (hfgh Z) (competitionMonitorBad_nonneg Z))
    competition_failure_decomposition m (X,true)
  rw [competition_monitor_steps_add P q _ _ hfgh competitionMonitorBad_nonneg,
    competition_monitor_steps_add P q _ _ hfg hh,
    competition_monitor_steps_add P q f g hf hg] at hm
  have hn := competition_monitor_noentry_bound eps k r delta hV heps hk (by linarith) hd q hq hbound m (X,true)
  have hrb := competition_monitor_resource_bound V (competitionWindowCap V) eps k r delta hV heps
    (by linarith) hk hk1 (by linarith) hr1 hd q hq hbound m (X,true)
  have hrt := competition_monitor_return_bound V (competitionWindowCap V) eps k r delta hV heps heps1
    hk hk1 hr hr1 hd hd1 q hq hbound m (X,true)
  have hw := competition_all_windows_probability V eps k r delta hV heps hk (by linarith) hd q hq hclock hbound m X
  change competitionMonitorSteps P q m competitionOperatingFailure (X,true) ≤ _
  change competitionMonitorSteps P q m f (X,true) ≤ f (X,true) at hn
  change competitionMonitorSteps P q m g (X,true) ≤ g (X,true)+(m:ℝ)*(4*resourceSource V) at hrb
  change competitionMonitorSteps P q m h (X,true) ≤ h (X,true)+(m:ℝ)*competitionReturnSource V at hrt
  change competitionMonitorSteps P q m competitionMonitorBad (X,true) ≤ _ at hw
  dsimp [f,g,h] at hn hrb hrt hm
  linarith

end
end RandomViability.Binding
