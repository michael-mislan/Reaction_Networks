import proofs.RandomViability.BindingCompetitionJointSupplyTails
import proofs.RandomViability.BindingCompetitionErrorBudget

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

def competitionSupplyCap (V : ℕ) : ℕ := ⌈2*(V:ℝ)*(500+competitionDuration V)⌉₊+1

theorem competition_supply_cap_strict (V : ℕ) :
    2*(V:ℝ)*(500+competitionDuration V)<(competitionSupplyCap V:ℝ) := by
  have hh := Nat.le_ceil (2*(V:ℝ)*(500+competitionDuration V))
  unfold competitionSupplyCap
  push_cast
  linarith

def competitionFullGood (V : ℕ) (X : CompetitionJointState V (competitionSupplyCap V)) : Prop :=
  (competitionWindowGood X.1.1 ∧ X.2=true) ∧
  (competitionServiceCount 0 X.1.2:ℝ) ≤ 2*(V:ℝ)*(500+competitionDuration V) ∧
  (competitionServiceCount 1 X.1.2:ℝ) ≤ 2*(V:ℝ)*(500+competitionDuration V) ∧
  (competitionServiceCount 2 X.1.2:ℝ) ≤ (V:ℝ)*(500+competitionDuration V)/8

def competitionFullFailure (V : ℕ) : CompetitionJointState V (competitionSupplyCap V) → ℝ :=
  FiniteKernel.eventIndicator {X | ¬competitionFullGood V X}

def competitionFullExpectation (V : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ))
    (f : CompetitionJointState V (competitionSupplyCap V) → ℝ) : ℝ :=
  competitionJointLaw (competitionJointStartupKernel V (competitionSupplyCap V) p hV)
    (competitionJointWindowKernel V (competitionSupplyCap V) p hV) (competitionClock V)
    (competitionFraction V) (competitionWindowNumber V) f (competitionJointInitial V (competitionSupplyCap V) hV)

theorem competition_full_failure_split (V : ℕ) (X : CompetitionJointState V (competitionSupplyCap V)) :
    competitionFullFailure V X ≤ competitionOperatingFailure (competitionJointForget X)+
      competitionJointServiceFailure 0 (2*(V:ℝ)*(500+competitionDuration V)) X+
      competitionJointServiceFailure 1 (2*(V:ℝ)*(500+competitionDuration V)) X+
      competitionJointServiceFailure 2 ((V:ℝ)*(500+competitionDuration V)/8) X := by
  have hn : competitionFullFailure V X ≤ 1 := (FiniteKernel.eventIndicator_bounds _ _).2
  have ho0 : 0 ≤ competitionOperatingFailure (competitionJointForget X) := (FiniteKernel.eventIndicator_bounds _ _).1
  have hu0 : 0 ≤ competitionJointServiceFailure 0 (2*(V:ℝ)*(500+competitionDuration V)) X :=
    (FiniteKernel.eventIndicator_bounds _ _).1
  have hw0 : 0 ≤ competitionJointServiceFailure 1 (2*(V:ℝ)*(500+competitionDuration V)) X :=
    (FiniteKernel.eventIndicator_bounds _ _).1
  have hf0 : 0 ≤ competitionJointServiceFailure 2 ((V:ℝ)*(500+competitionDuration V)/8) X :=
    (FiniteKernel.eventIndicator_bounds _ _).1
  by_cases ho : ¬(competitionWindowGood X.1.1 ∧ X.2=true)
  · have he : competitionOperatingFailure (competitionJointForget X)=1 := if_pos ho
    linarith
  · by_cases hu : 2*(V:ℝ)*(500+competitionDuration V)<(competitionServiceCount 0 X.1.2:ℝ)
    · have he : competitionJointServiceFailure 0 (2*(V:ℝ)*(500+competitionDuration V)) X=1 := if_pos hu
      linarith
    · by_cases hw : 2*(V:ℝ)*(500+competitionDuration V)<(competitionServiceCount 1 X.1.2:ℝ)
      · have he : competitionJointServiceFailure 1 (2*(V:ℝ)*(500+competitionDuration V)) X=1 := if_pos hw
        linarith
      · by_cases hf : (V:ℝ)*(500+competitionDuration V)/8<(competitionServiceCount 2 X.1.2:ℝ)
        · have he : competitionJointServiceFailure 2 ((V:ℝ)*(500+competitionDuration V)/8) X=1 := if_pos hf
          linarith
        · have hg : competitionFullGood V X :=
            ⟨not_not.mp ho,le_of_not_gt hu,le_of_not_gt hw,le_of_not_gt hf⟩
          have he : competitionFullFailure V X=0 := if_neg (not_not.mpr hg)
          linarith

theorem competition_full_failure_bound (V : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) :
    competitionFullExpectation V p hV (competitionFullFailure V) ≤ competitionRootError V := by
  let C := competitionSupplyCap V
  let S := competitionJointStartupKernel V C p hV
  let Q := competitionJointWindowKernel V C p hV
  let q : ℝ≥0 := competitionClock V
  let s := competitionFraction V
  let m := competitionWindowNumber V
  let X := competitionJointInitial V C hV
  let f : CompetitionJointState V C → ℝ := fun Z => competitionOperatingFailure (competitionJointForget Z)
  let g : CompetitionJointState V C → ℝ := competitionJointServiceFailure 0 (2*(V:ℝ)*(500+competitionDuration V))
  let h : CompetitionJointState V C → ℝ := competitionJointServiceFailure 1 (2*(V:ℝ)*(500+competitionDuration V))
  let j : CompetitionJointState V C → ℝ := competitionJointServiceFailure 2 ((V:ℝ)*(500+competitionDuration V)/8)
  have hf (Z) : 0 ≤ f Z := (FiniteKernel.eventIndicator_bounds _ _).1
  have hg (Z) : 0 ≤ g Z := (FiniteKernel.eventIndicator_bounds _ _).1
  have hh (Z) : 0 ≤ h Z := (FiniteKernel.eventIndicator_bounds _ _).1
  have hj (Z) : 0 ≤ j Z := (FiniteKernel.eventIndicator_bounds _ _).1
  have hfg (Z) : 0 ≤ f Z+g Z := add_nonneg (hf Z) (hg Z)
  have hfgh (Z) : 0 ≤ f Z+g Z+h Z := add_nonneg (hfg Z) (hh Z)
  have hm := competition_joint_law_mono Q S q s m (competitionFullFailure V) (fun Z => f Z+g Z+h Z+j Z)
    (fun Z => (FiniteKernel.eventIndicator_bounds _ _).1)
    (fun Z => add_nonneg (hfgh Z) (hj Z)) (competition_full_failure_split V) X
  rw [competition_joint_law_add Q S q s m _ _ hfgh hj,
    competition_joint_law_add Q S q s m _ _ hfg hh,
    competition_joint_law_add Q S q s m f g hf hg] at hm
  have hop : competitionJointLaw S Q q s m f X=competitionContractOperatingFailure V p hV :=
    competition_joint_operating_projection V C p hV s m X
  have hoper := competition_contract_operating_bound V p hV
  change competitionContractOperatingFailure V p hV ≤ competitionOperatingError V at hoper
  have ht : 500+(m:ℝ)+(s:ℝ)=500+competitionDuration V := by
    dsimp [m,s]
    linarith [competition_horizon_partition V]
  have hu := competition_joint_food_tail V C p hV 0 (by decide) s m
  have hw := competition_joint_food_tail V C p hV 1 (by decide) s m
  have hd := competition_joint_fuel_tail V C p hV s m
  rw [ht] at hu hw hd
  change competitionJointLaw S Q q s m g X ≤ _ at hu
  change competitionJointLaw S Q q s m h X ≤ _ at hw
  change competitionJointLaw S Q q s m j X ≤ _ at hd
  rw [hop] at hm
  change competitionJointLaw S Q q s m (competitionFullFailure V) X ≤ _
  unfold competitionRootError competitionSupplyError
  linarith

/-- Joint finite-law endpoint for operation and the declared gross supply budgets.
Identification with literal histories uses the cap and first-exit lemmas. -/
theorem competition_supplied_operating_probability (V : ℕ) (p : CompetitionRateBox) (hV : 100000000 ≤ V) :
    1-2*Real.exp (-(2/100000000)*(V:ℝ)) ≤
      competitionFullExpectation V p (by
        have hv : (100000000:ℝ)≤V := by exact_mod_cast hV
        linarith)
        (FiniteKernel.eventIndicator {X | competitionFullGood V X}) := by
  have hv : 0 < (V:ℝ) := by
    have hh : (100000000:ℝ)≤V := by exact_mod_cast hV
    linarith
  let C := competitionSupplyCap V
  let S := competitionJointStartupKernel V C p hv
  let Q := competitionJointWindowKernel V C p hv
  let f : CompetitionJointState V C → ℝ := FiniteKernel.eventIndicator {X | competitionFullGood V X}
  have hf (X) : 0 ≤ f X := (FiniteKernel.eventIndicator_bounds _ _).1
  have hg (X) : 0 ≤ competitionFullFailure V X := (FiniteKernel.eventIndicator_bounds _ _).1
  have he : (fun X => f X+competitionFullFailure V X)=(fun _ => 1) := by
    funext X
    by_cases hh : competitionFullGood V X <;> simp [f,competitionFullFailure,FiniteKernel.eventIndicator,hh]
  have hadd := competition_joint_law_add Q S (competitionClock V) (competitionFraction V) (competitionWindowNumber V)
    f (competitionFullFailure V) hf hg (competitionJointInitial V C hv)
  rw [he,competition_joint_law_const] at hadd
  have hbad := (competition_full_failure_bound V p hv).trans (competition_root_error_bound V hV)
  change 1=competitionFullExpectation V p hv f+competitionFullExpectation V p hv (competitionFullFailure V) at hadd
  change 1-2*Real.exp (-(2/100000000)*(V:ℝ)) ≤ competitionFullExpectation V p hv f
  linarith

end
end RandomViability.Binding
