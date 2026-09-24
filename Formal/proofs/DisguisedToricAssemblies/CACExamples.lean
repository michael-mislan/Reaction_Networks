import proofs.DisguisedToricAssemblies.LiteralRealization

namespace DisguisedToricAssemblies
open CoreCouplingCAC

noncomputable def positiveRates : Rates := ⟨7/16,7/16,1,12/25,1/2,1⟩
noncomputable def positiveState : State := ⟨1/2,1/2,5/8,13/48⟩
noncomputable def negativeRates : Rates := ⟨41729/400000,115951/800000,1/100,5,5,10⟩
noncomputable def negativeState : State := ⟨703/2000,9/50,19/100,19/1250⟩

theorem positive_example : positiveRates.Positive ∧ positiveState.Positive ∧
    Stationary positiveRates positiveState ∧ RealizableAt positiveRates positiveState := by
  have hp : positiveRates.Positive := by norm_num [positiveRates,Rates.Positive]
  have hx : positiveState.Positive := by norm_num [positiveState,State.Positive]
  have hs : Stationary positiveRates positiveState := by
    norm_num [Stationary,positiveRates,positiveState,fA,fB,fZ,fH]
  refine ⟨hp,hx,hs,(cac_state_characterization _ _ hp hx).mpr ⟨hs,?_,?_⟩⟩
  · norm_num [positiveState]
  · norm_num [positiveState,positiveRates]

theorem positive_AB_margins :
    -(positiveState.A-positiveState.B*positiveState.z)+
      2*positiveRates.e*(positiveState.B-positiveState.A^2) = (1/16 : ℝ) ∧
    (positiveState.A-positiveState.B*positiveState.z)-
      positiveRates.e*(positiveState.B-positiveState.A^2) = (1/16 : ℝ) := by
  norm_num [positiveState,positiveRates]

theorem negative_stationary : negativeRates.Positive ∧ negativeState.Positive ∧
    Stationary negativeRates negativeState := by
  norm_num [negativeRates,negativeState,Rates.Positive,State.Positive,Stationary,fA,fB,fZ,fH]

theorem negative_unique_stationary (x : State) (hx : x.Positive)
    (hs : Stationary negativeRates x) : x = negativeState :=
  loss_regime_unistationary negativeRates negative_stationary.1 (by norm_num [negativeRates])
    x negativeState hx negative_stationary.2.1 hs negative_stationary.2.2

theorem negative_not_disguised : ¬ DisguisedToric negativeRates := by
  rintro ⟨x,hx,hr⟩
  obtain ⟨hs,_,hJ⟩ := (cac_state_characterization _ _ negative_stationary.1 hx).mp hr
  have heq := negative_unique_stationary x hx hs
  rw [heq] at hJ
  norm_num [negativeRates,negativeState] at hJ

theorem negative_exact_dual :
    2*(negativeState.B-negativeRates.e*(negativeState.B-negativeState.A^2)) =
      (-81791/400000 : ℝ) := by norm_num [negativeRates,negativeState]

theorem safe_region (p : Rates) (hp : p.Positive) (hd : 1 ≤ p.d) (he : p.e ≤ 1) :
    DisguisedToric p := by
  have hu := hp.2.2.1
  have hv := hp.2.2.2.1
  have hdp := hp.2.2.2.2.2
  have hnum : p.u*(1-p.d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.le (by linarith)
  have hc : admissibleCut p = 0 :=
    max_eq_left (div_nonpos_of_nonpos_of_nonneg hnum (by positivity))
  apply (cacParameterLocus p hp).mpr
  refine ⟨?_,Or.inl he⟩
  rw [hc]
  exact (residual_zero_negative p hp).le

theorem toric_forbids_ZH_productivity (p : Rates) (x : State)
    (hp : p.Positive) (hx : x.Positive) (hr : RealizableAt p x) : (coreZH p x).1 ≤ 0 := by
  obtain ⟨hs,hK,_⟩ := (cac_state_characterization p x hp hx).mp hr
  have hz := hs.2.2.1
  dsimp [fZ] at hz
  dsimp [coreZH]
  linarith

end DisguisedToricAssemblies
