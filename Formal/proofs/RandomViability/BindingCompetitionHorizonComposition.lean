import proofs.RandomViability.BindingCompetitionStartupComposition
import proofs.RandomViability.BindingCompetitionHorizonWindows

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

/-- Startup, m completed windows, then an arbitrary final fractional segment. -/
def competitionHorizonFailure (V : ℕ) (S : FiniteKernel (CompetitionCounts V))
    (P : FiniteKernel (CompetitionWindowState V (competitionWindowCap V)))
    (q s : ℝ≥0) (m : ℕ) (X : CompetitionCounts V) : ℝ :=
  S.poissonized (q*500) (fun Z => competitionMonitorSteps P q m (competitionFinalFailure P q s) ((Z,0),true)) X

theorem competition_startup_horizon (V q : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (hq : 0 < q)
    (hclock : (V:ℝ)/27000 ≤ q)
    (hb : ∀ X, (competitionModel V eps k r delta hV heps hk (by linarith) hd).total X ≤ q)
    (he : ∀ X, (competitionEntryModel V ((V:ℝ)/2500) eps k r delta hV heps hk (by linarith) hd).total X ≤ q)
    (hw : ∀ X, (competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk (by linarith) hd).total X ≤ q)
    (s : ℝ≥0) (m : ℕ) :
    competitionHorizonFailure V
      ((competitionModel V eps k r delta hV heps hk (by linarith) hd).uniformize q (by exact_mod_cast hq) hb)
      ((competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk (by linarith) hd).uniformize q (by exact_mod_cast hq) hw)
      q s m (competitionFoodInitial V hV) ≤
      Real.exp ((V:ℝ)/2500/40000-399*((14/25)*eps*V*(2/25)))+Real.exp (-(q:ℝ)/500000)+
      4*Real.exp (-(V:ℝ)/1000)+Real.exp (-(V:ℝ)/62500)+
      (500+(m:ℝ)+(s:ℝ))*(4*resourceSource V+competitionReturnSource V)+
      (m:ℝ)*Real.exp (1/8-(13/1080000)*(V:ℝ)) := by
  let M := competitionModel V eps k r delta hV heps hk (by linarith) hd
  let S := M.uniformize q (by exact_mod_cast hq) hb
  let P := (competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk (by linarith) hd).uniformize q (by exact_mod_cast hq) hw
  let X := competitionFoodInitial V hV
  let f : CompetitionCounts V → ℝ := competitionNoEntry
  let g : CompetitionCounts V → ℝ := fun Z => resourcePotential V (boxCounts (competitionCounts Z))
  let h : CompetitionCounts V → ℝ := competitionTrackedReturnPotential
  let b : ℝ := ((m:ℝ)+(s:ℝ))*(4*resourceSource V+competitionReturnSource V)+(m:ℝ)*Real.exp (1/8-(13/1080000)*(V:ℝ))
  have hf (Z) : 0 ≤ f Z := competition_noentry_nonneg _
  have hg (Z) : 0 ≤ g Z := resourcePotential_nonneg V _
  have hh (Z) : 0 ≤ h Z := competition_tracked_return_nonneg _
  have hfg (Z) : 0 ≤ f Z+g Z := add_nonneg (hf Z) (hg Z)
  have hfgh (Z) : 0 ≤ f Z+g Z+h Z := add_nonneg (hfg Z) (hh Z)
  have hbn : 0 ≤ b := by unfold b resourceSource competitionReturnSource; positivity
  have hpt (Z : CompetitionCounts V) : competitionMonitorSteps P q m (competitionFinalFailure P q s) ((Z,0),true) ≤ f Z+g Z+h Z+b := by
    have hp := competition_horizon_windows V eps k r delta hV heps heps1 hk hk1 hr hr1 hd hd1
      q s (by exact_mod_cast hq) (by simpa only [NNReal.coe_natCast] using hclock)
      (by simpa only [NNReal.coe_natCast] using hw) m (Z,0)
    dsimp [b,f,g,h]
    convert hp using 1
    ring
  have hon (Z : CompetitionCounts V) : 0 ≤ competitionMonitorSteps P q m (competitionFinalFailure P q s) ((Z,0),true) := by
    apply competition_monitor_steps_nonneg
    intro Y
    apply P.poissonized_nonneg
    intro Z
    unfold competitionOperatingFailure FiniteKernel.eventIndicator
    split_ifs <;> norm_num
  have hm := S.poissonized_mono ((q:ℝ≥0)*500) _ (fun Z => f Z+g Z+h Z+b) hon
    (fun Z => add_nonneg (hfgh Z) hbn) hpt X
  rw [S.poissonized_add _ _ _ hfgh (fun _ => hbn),
    S.poissonized_add _ _ _ hfg hh,S.poissonized_add _ f g hf hg,S.poissonized_const] at hm
  have hen := competition_tracked_entry_deadline V q eps k r delta hV heps heps1 hk hk1 hr hr1 hd hd1 hq hb he X rfl
  change S.poissonized ((q:ℝ≥0)*500) f X ≤ _ at hen
  have hrg := S.poissonized_drift_bound ((q:ℝ≥0)*500) g ((4*resourceSource V)/(q:ℝ)) hg
    (M.uniformize_drift q (by exact_mod_cast hq) hb g _
      (competition_resource_foster V eps k r delta hV heps (by linarith) hk hk1 (by linarith) hr1 hd)) X
  have hrt := S.poissonized_drift_bound ((q:ℝ≥0)*500) h (competitionReturnSource V/(q:ℝ)) hh
    (M.uniformize_drift q (by exact_mod_cast hq) hb h _
      (competition_tracked_return_foster V eps k r delta hV heps heps1 hk hk1 hr hr1 hd hd1)) X
  have hqn : (q:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have heq (c : ℝ) : (((q:ℝ≥0)*500:ℝ≥0):ℝ)*(c/(q:ℝ))=500*c := by
    norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat]
    field_simp
  rw [heq] at hrg hrt
  have hgX : g X=4*Real.exp (-(V:ℝ)/1000) := foodInitial_potential V
  have hhX : h X=Real.exp (-(V:ℝ)/62500) := by simp [h,X,competitionTrackedReturnPotential,competitionFoodInitial,competitionPhase]
  rw [hgX] at hrg
  rw [hhX] at hrt
  change S.poissonized ((q:ℝ≥0)*500) (fun Z => competitionMonitorSteps P q m (competitionFinalFailure P q s) ((Z,0),true)) X ≤ _
  dsimp [b] at hm
  linarith

end
end RandomViability.Binding
