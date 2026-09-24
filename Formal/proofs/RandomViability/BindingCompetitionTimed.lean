import proofs.RandomViability.BindingCompetitionSuppliedOperating

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

def competitionTimedOperatingFailure (V : ℕ) (s : ℝ≥0) (m : ℕ) (p : CompetitionRateBox) (hV : 0<(V:ℝ)) : ℝ :=
  competitionHorizonFailure V (competitionContractKernel V p hV) (competitionContractWindowKernel V p hV)
    (competitionClock V) s m (competitionFoodInitial V hV)

theorem competition_timed_operating_bound (V : ℕ) (s : ℝ≥0) (m : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) :
    competitionTimedOperatingFailure V s m p hV ≤
      Real.exp (-(8047/312500000000)*(V:ℝ))+Real.exp (-3000*(V:ℝ)/500000)+
      4*Real.exp (-(V:ℝ)/1000)+Real.exp (-(V:ℝ)/62500)+
      (500+(m:ℝ)+(s:ℝ))*(4*resourceSource V+competitionReturnSource V)+
      (m:ℝ)*Real.exp (1/8-(13/1080000)*(V:ℝ)) := by
  have he (N : BoxCounts V) :
      (competitionEntryModel V ((V:ℝ)/2500) (1/500000000) (1/p.K) p.r p.delta hV
        (by norm_num) p.inv_nonneg p.r_nonneg p.delta_nonneg).total N ≤ (competitionClock V:ℝ) := by
    simpa only [competitionClock,Nat.cast_mul,Nat.cast_ofNat] using
      competition_entry_total_bound V ((V:ℝ)/2500) (1/500000000) (1/p.K) p.r p.delta hV
        (by norm_num) (by norm_num) p.inv_nonneg p.inv_upper p.r_nonneg p.r_upper p.delta_nonneg p.delta_local N
  have hc : (V:ℝ)/27000 ≤ (competitionClock V:ℝ) := by
    simp only [competitionClock,Nat.cast_mul,Nat.cast_ofNat]
    linarith
  have hh := competition_startup_horizon V (competitionClock V) (1/500000000) (1/p.K) p.r p.delta hV
    (by norm_num) (by norm_num) p.inv_nonneg p.inv_upper p.r_lower p.r_upper p.delta_nonneg p.delta_local
    (competitionClock_pos V hV) hc (competition_contract_total V p hV) he (competition_contract_window_total V p hV)
    s m
  rw [competition_entry_exponent] at hh
  simpa only [competitionTimedOperatingFailure,competitionContractKernel,competitionContractWindowKernel,
    competitionContractModel,competitionContractWindowModel,competitionClock,Nat.cast_mul,Nat.cast_ofNat,neg_mul] using hh

def competitionTimedOperatingError (V : ℕ) (s : ℝ≥0) (m : ℕ) : ℝ :=
  Real.exp (-(8047/312500000000)*(V:ℝ))+Real.exp (-3000*(V:ℝ)/500000)+
  4*Real.exp (-(V:ℝ)/1000)+Real.exp (-(V:ℝ)/62500)+
  (500+(m:ℝ)+(s:ℝ))*(4*resourceSource V+competitionReturnSource V)+
  (m:ℝ)*Real.exp (1/8-(13/1080000)*(V:ℝ))

def competitionTimedSupplyError (V : ℕ) (s : ℝ≥0) (m : ℕ) : ℝ :=
  2*Real.exp (-(2*Real.log 2-1)*(V:ℝ)*(500+(m:ℝ)+(s:ℝ)))+
  Real.exp (-(V:ℝ)*(500+(m:ℝ)+(s:ℝ))/200)

def competitionTimedRootError (V : ℕ) (s : ℝ≥0) (m : ℕ) : ℝ := competitionTimedOperatingError V s m+competitionTimedSupplyError V s m

def competitionTimedSupplyCap (V : ℕ) (s : ℝ≥0) (m : ℕ) : ℕ := ⌈2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))⌉₊+1

theorem competition_timed_supply_cap_strict (V : ℕ) (s : ℝ≥0) (m : ℕ) :
    2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))<(competitionTimedSupplyCap V s m:ℝ) := by
  have hh := Nat.le_ceil (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ)))
  unfold competitionTimedSupplyCap
  push_cast
  linarith

def competitionTimedFullGood (V : ℕ) (s : ℝ≥0) (m : ℕ) (X : CompetitionJointState V (competitionTimedSupplyCap V s m)) : Prop :=
  (competitionWindowGood X.1.1 ∧ X.2=true) ∧
  (competitionServiceCount 0 X.1.2:ℝ) ≤ 2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ)) ∧
  (competitionServiceCount 1 X.1.2:ℝ) ≤ 2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ)) ∧
  (competitionServiceCount 2 X.1.2:ℝ) ≤ (V:ℝ)*(500+(m:ℝ)+(s:ℝ))/8

def competitionTimedFullFailure (V : ℕ) (s : ℝ≥0) (m : ℕ) : CompetitionJointState V (competitionTimedSupplyCap V s m) → ℝ :=
  FiniteKernel.eventIndicator {X | ¬competitionTimedFullGood V s m X}

def competitionTimedFullExpectation (V : ℕ) (s : ℝ≥0) (m : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ))
    (f : CompetitionJointState V (competitionTimedSupplyCap V s m) → ℝ) : ℝ :=
  competitionJointLaw (competitionJointStartupKernel V (competitionTimedSupplyCap V s m) p hV)
    (competitionJointWindowKernel V (competitionTimedSupplyCap V s m) p hV) (competitionClock V)
    s m f (competitionJointInitial V (competitionTimedSupplyCap V s m) hV)

theorem competition_timed_full_failure_split (V : ℕ) (s : ℝ≥0) (m : ℕ) (X : CompetitionJointState V (competitionTimedSupplyCap V s m)) :
    competitionTimedFullFailure V s m X ≤ competitionOperatingFailure (competitionJointForget X)+
      competitionJointServiceFailure 0 (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))) X+
      competitionJointServiceFailure 1 (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))) X+
      competitionJointServiceFailure 2 ((V:ℝ)*(500+(m:ℝ)+(s:ℝ))/8) X := by
  have hn : competitionTimedFullFailure V s m X ≤ 1 := (FiniteKernel.eventIndicator_bounds _ _).2
  have ho0 : 0 ≤ competitionOperatingFailure (competitionJointForget X) := (FiniteKernel.eventIndicator_bounds _ _).1
  have hu0 : 0 ≤ competitionJointServiceFailure 0 (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))) X :=
    (FiniteKernel.eventIndicator_bounds _ _).1
  have hw0 : 0 ≤ competitionJointServiceFailure 1 (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))) X :=
    (FiniteKernel.eventIndicator_bounds _ _).1
  have hf0 : 0 ≤ competitionJointServiceFailure 2 ((V:ℝ)*(500+(m:ℝ)+(s:ℝ))/8) X :=
    (FiniteKernel.eventIndicator_bounds _ _).1
  by_cases ho : ¬(competitionWindowGood X.1.1 ∧ X.2=true)
  · have he : competitionOperatingFailure (competitionJointForget X)=1 := if_pos ho
    linarith
  · by_cases hu : 2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))<(competitionServiceCount 0 X.1.2:ℝ)
    · have he : competitionJointServiceFailure 0 (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))) X=1 := if_pos hu
      linarith
    · by_cases hw : 2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))<(competitionServiceCount 1 X.1.2:ℝ)
      · have he : competitionJointServiceFailure 1 (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))) X=1 := if_pos hw
        linarith
      · by_cases hf : (V:ℝ)*(500+(m:ℝ)+(s:ℝ))/8<(competitionServiceCount 2 X.1.2:ℝ)
        · have he : competitionJointServiceFailure 2 ((V:ℝ)*(500+(m:ℝ)+(s:ℝ))/8) X=1 := if_pos hf
          linarith
        · have hg : competitionTimedFullGood V s m X :=
            ⟨not_not.mp ho,le_of_not_gt hu,le_of_not_gt hw,le_of_not_gt hf⟩
          have he : competitionTimedFullFailure V s m X=0 := if_neg (not_not.mpr hg)
          linarith

theorem competition_timed_full_failure_bound (V : ℕ) (s : ℝ≥0) (m : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) :
    competitionTimedFullExpectation V s m p hV (competitionTimedFullFailure V s m) ≤ competitionTimedRootError V s m := by
  let C := competitionTimedSupplyCap V s m
  let S := competitionJointStartupKernel V C p hV
  let Q := competitionJointWindowKernel V C p hV
  let q : ℝ≥0 := competitionClock V
  let X := competitionJointInitial V C hV
  let f : CompetitionJointState V C → ℝ := fun Z => competitionOperatingFailure (competitionJointForget Z)
  let g : CompetitionJointState V C → ℝ := competitionJointServiceFailure 0 (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ)))
  let h : CompetitionJointState V C → ℝ := competitionJointServiceFailure 1 (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ)))
  let j : CompetitionJointState V C → ℝ := competitionJointServiceFailure 2 ((V:ℝ)*(500+(m:ℝ)+(s:ℝ))/8)
  have hf (Z) : 0 ≤ f Z := (FiniteKernel.eventIndicator_bounds _ _).1
  have hg (Z) : 0 ≤ g Z := (FiniteKernel.eventIndicator_bounds _ _).1
  have hh (Z) : 0 ≤ h Z := (FiniteKernel.eventIndicator_bounds _ _).1
  have hj (Z) : 0 ≤ j Z := (FiniteKernel.eventIndicator_bounds _ _).1
  have hfg (Z) : 0 ≤ f Z+g Z := add_nonneg (hf Z) (hg Z)
  have hfgh (Z) : 0 ≤ f Z+g Z+h Z := add_nonneg (hfg Z) (hh Z)
  have hm := competition_joint_law_mono Q S q s m (competitionTimedFullFailure V s m) (fun Z => f Z+g Z+h Z+j Z)
    (fun Z => (FiniteKernel.eventIndicator_bounds _ _).1)
    (fun Z => add_nonneg (hfgh Z) (hj Z)) (competition_timed_full_failure_split V s m) X
  rw [competition_joint_law_add Q S q s m _ _ hfgh hj,
    competition_joint_law_add Q S q s m _ _ hfg hh,
    competition_joint_law_add Q S q s m f g hf hg] at hm
  have hop : competitionJointLaw S Q q s m f X=competitionTimedOperatingFailure V s m p hV :=
    competition_joint_operating_projection V C p hV s m X
  have hoper := competition_timed_operating_bound V s m p hV
  change competitionTimedOperatingFailure V s m p hV ≤ competitionTimedOperatingError V s m at hoper
  have hu := competition_joint_food_tail V C p hV 0 (by decide) s m
  have hw := competition_joint_food_tail V C p hV 1 (by decide) s m
  have hd := competition_joint_fuel_tail V C p hV s m
  change competitionJointLaw S Q q s m g X ≤ _ at hu
  change competitionJointLaw S Q q s m h X ≤ _ at hw
  change competitionJointLaw S Q q s m j X ≤ _ at hd
  rw [hop] at hm
  change competitionJointLaw S Q q s m (competitionTimedFullFailure V s m) X ≤ _
  unfold competitionTimedRootError competitionTimedSupplyError
  linarith


theorem competition_timed_supplied_probability (V : ℕ) (s : ℝ≥0) (m : ℕ)
    (p : CompetitionRateBox) (hV : 0<(V:ℝ)) :
    1-competitionTimedRootError V s m ≤ competitionTimedFullExpectation V s m p hV
      (FiniteKernel.eventIndicator {X | competitionTimedFullGood V s m X}) := by
  let C := competitionTimedSupplyCap V s m
  let S := competitionJointStartupKernel V C p hV
  let Q := competitionJointWindowKernel V C p hV
  let f : CompetitionJointState V C → ℝ := FiniteKernel.eventIndicator {X | competitionTimedFullGood V s m X}
  have hf (X) : 0 ≤ f X := (FiniteKernel.eventIndicator_bounds _ _).1
  have hg (X) : 0 ≤ competitionTimedFullFailure V s m X := (FiniteKernel.eventIndicator_bounds _ _).1
  have he : (fun X => f X+competitionTimedFullFailure V s m X)=(fun _ => 1) := by
    funext X
    by_cases hh : competitionTimedFullGood V s m X <;> simp [f,competitionTimedFullFailure,FiniteKernel.eventIndicator,hh]
  have hadd := competition_joint_law_add Q S (competitionClock V) s m
    f (competitionTimedFullFailure V s m) hf hg (competitionJointInitial V C hV)
  rw [he,competition_joint_law_const] at hadd
  have hbad := competition_timed_full_failure_bound V s m p hV
  change 1=competitionTimedFullExpectation V s m p hV f+competitionTimedFullExpectation V s m p hV (competitionTimedFullFailure V s m) at hadd
  change 1-competitionTimedRootError V s m ≤ competitionTimedFullExpectation V s m p hV f
  linarith

end
end RandomViability.Binding
