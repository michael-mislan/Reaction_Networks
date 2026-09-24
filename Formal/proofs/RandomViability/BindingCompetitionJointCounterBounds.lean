import proofs.RandomViability.BindingCompetitionJointLinear

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

def competitionJointCounterPotential {V C : ℕ} (mode : Fin 3) (theta : ℝ) (X : CompetitionJointState V C) : ℝ :=
  Real.exp (theta*(competitionServiceCount mode X.1.2:ℝ))

theorem competition_joint_counter_growth (V C : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ))
    (mode : Fin 3) (theta : ℝ) (htheta : 0 ≤ theta) (s : ℝ≥0) (m : ℕ)
    (X : CompetitionCounts V × CompetitionGrossCounters C) :
    competitionJointLaw (competitionJointStartupKernel V C p hV) (competitionJointWindowKernel V C p hV)
      (competitionClock V) s m (competitionJointCounterPotential mode theta) X ≤
      Real.exp (competitionServiceRateBound V mode*(Real.exp theta-1)*(500+(m:ℝ)+(s:ℝ)))*
        Real.exp (theta*(competitionServiceCount mode X.2:ℝ)) := by
  let q : ℝ≥0 := competitionClock V
  let S := competitionJointStartupKernel V C p hV
  let Q := competitionJointWindowKernel V C p hV
  let f : CompetitionJointState V C → ℝ := competitionJointCounterPotential mode theta
  let a : ℝ := competitionServiceRateBound V mode*(Real.exp theta-1)
  have hf (Z) : 0 ≤ f Z := (Real.exp_pos _).le
  have hq : 0 < (q:ℝ) := by dsimp [q]; exact_mod_cast competitionClock_pos V hV
  have hwindow (t : ℝ≥0) (Z : CompetitionWindowState V (competitionWindowCap V) × CompetitionGrossCounters C) :
      Q.poissonized (q*t) (competitionCounterPotential C mode theta) Z ≤
        Real.exp (a*(t:ℝ))*competitionCounterPotential C mode theta Z := by
    exact competition_counter_exponential_time C (competitionContractWindowModel V p hV) competitionServiceLabel
      mode theta (competitionServiceRateBound V mode) htheta (competitionServiceRateBound_nonneg V mode)
      (competition_window_service_bound V (competitionWindowCap V) (1/500000000) (1/p.K) p.r p.delta hV
        (by norm_num) (by norm_num) p.inv_nonneg p.r_nonneg p.delta_nonneg p.delta_upper mode)
      q t hq (by simpa only [q,NNReal.coe_natCast] using competition_contract_window_total V p hV) Z
  have hstartup (Z : CompetitionCounts V × CompetitionGrossCounters C) :
      S.poissonized (q*500) (competitionCounterPotential C mode theta) Z ≤
        Real.exp (a*500)*competitionCounterPotential C mode theta Z := by
    have hh := competition_counter_exponential_time C (competitionContractModel V p hV) competitionServiceLabel
      mode theta (competitionServiceRateBound V mode) htheta (competitionServiceRateBound_nonneg V mode)
      (competition_model_service_bound V (1/500000000) (1/p.K) p.r p.delta hV
        (by norm_num) (by norm_num) p.inv_nonneg p.r_nonneg p.delta_nonneg p.delta_upper mode)
      q 500 hq (by simpa only [q,NNReal.coe_natCast] using competition_contract_total V p hV) Z
    simpa only [NNReal.coe_ofNat] using hh
  have hstep (Z : CompetitionJointState V C) : competitionJointAdvance Q q f Z ≤ Real.exp a*f Z := by
    have hh := hwindow 1 Z.1
    simpa only [mul_one,NNReal.coe_one,one_mul] using hh
  have hn (Z : CompetitionJointState V C) : competitionJointSteps Q q m f Z ≤ Real.exp ((m:ℝ)*a)*f Z := by
    have hh := competition_joint_steps_growth Q q f hf (Real.exp a) (Real.exp_pos _).le hstep m Z
    simpa only [Real.exp_nat_mul] using hh
  have hfinal (Z : CompetitionJointState V C) : competitionJointFinal Q q s f Z ≤ Real.exp (a*(s:ℝ))*f Z :=
    hwindow s Z.1
  have hfinal_nonneg (Z : CompetitionJointState V C) : 0 ≤ competitionJointFinal Q q s f Z :=
    Q.poissonized_nonneg (q*s) _ (fun W => hf (W,Z.2)) Z.1
  have hpost (Z : CompetitionJointState V C) :
      competitionJointSteps Q q m (competitionJointFinal Q q s f) Z ≤
        Real.exp (a*((m:ℝ)+(s:ℝ)))*f Z := by
    have hh := competition_joint_steps_mono Q q _ (fun W => Real.exp (a*(s:ℝ))*f W)
      hfinal_nonneg (fun W => mul_nonneg (Real.exp_pos _).le (hf W)) hfinal m Z
    rw [competition_joint_steps_scale] at hh
    have ht := mul_le_mul_of_nonneg_left (hn Z) (Real.exp_pos (a*(s:ℝ))).le
    apply hh.trans (ht.trans_eq ?_)
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hm := S.poissonized_mono (q*500) _
    (fun Z => Real.exp (a*((m:ℝ)+(s:ℝ)))*competitionCounterPotential C mode theta Z)
    (fun Z => competition_joint_steps_nonneg Q q _ hfinal_nonneg m _)
    (fun Z => by unfold competitionCounterPotential; positivity)
    (fun Z => hpost (((Z.1,0),Z.2),true)) X
  rw [S.poissonized_scale] at hm
  have ht := mul_le_mul_of_nonneg_left (hstartup X) (Real.exp_pos (a*((m:ℝ)+(s:ℝ)))).le
  change competitionJointLaw S Q q s m f X ≤ _
  apply hm.trans (ht.trans_eq ?_)
  rw [← mul_assoc,← Real.exp_add]
  congr 2
  dsimp [a]
  ring

end
end RandomViability.Binding
