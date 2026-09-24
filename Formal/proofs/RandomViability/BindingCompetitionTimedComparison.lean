import proofs.RandomViability.BindingCompetitionComparison
import proofs.RandomViability.BindingCompetitionTimed

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

theorem competition_timed_disabled_creation_probability (V C H : ℕ) (p : CompetitionRateBox)
    (hH : 1≤H) (hv : 0<(V:ℝ)) :
    (competitionDisabledCountKernel V C p hv).poissonized
      ((competitionClock V:ℝ≥0)*(500+(H:ℝ≥0)))
      (FiniteKernel.eventIndicator {X | (V:ℝ)*(H:ℝ)/21000 <
        (competitionServiceCount 0 X.2:ℝ)}) (foodInitial V,fun _=>0) ≤
      Real.exp (-(V:ℝ)*(H:ℝ)/25000) := by
  have hh := competition_counter_probability C (competitionDisabledModel V p hv) competitionCreationLabel
    0 1 (competitionDisabledLambda*(V:ℝ)) ((V:ℝ)*(H:ℝ)/21000)
    (by norm_num) (by unfold competitionDisabledLambda; positivity)
    (competition_disabled_creation_rate V p hv) (competitionClock V)
    (500+(H:ℝ≥0))
    (by exact_mod_cast competitionClock_pos V hv) (competition_disabled_total V p hv)
    (foodInitial V,fun _=>0)
  norm_num only [competitionCounterPotential,competitionServiceCount,Fin.ext_iff,ite_false,ite_true,Fin.val_zero,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one,NNReal.coe_add,NNReal.coe_ofNat] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  change -1*((V:ℝ)*(H:ℝ)/21000)+competitionDisabledLambda*(V:ℝ)*(Real.exp 1-1)*(500+(H:ℝ)) ≤ -(V:ℝ)*(H:ℝ)/25000
  have ht : 500+(H:ℝ)≤502*(H:ℝ) := by
    have hh : (1:ℝ)≤H := by exact_mod_cast hH
    linarith
  have hn : 0 ≤ competitionDisabledLambda*(V:ℝ) := by unfold competitionDisabledLambda; positivity
  have he := mul_le_mul_of_nonneg_left (show Real.exp 1-1 ≤ (2:ℝ) by linarith [Real.exp_one_lt_three]) hn
  have hm := mul_le_mul_of_nonneg_right he (show 0≤500+(H:ℝ) by positivity)
  have hw := mul_le_mul_of_nonneg_left ht (show 0≤2*competitionDisabledLambda*(V:ℝ) by unfold competitionDisabledLambda; positivity)
  have hp : 0≤(V:ℝ)*(H:ℝ) := by positivity
  dsimp [competitionDisabledLambda] at hm hw ⊢
  nlinarith only [hm,hw,hp]

def competitionTimedDisabledPossible (V C H : ℕ) (X : BoxCounts V × CompetitionGrossCounters C) : Prop :=
  (V:ℝ)*(H:ℝ)/21000 < (competitionServiceCount 0 X.2:ℝ) ∨
    ¬resourceGood (boxCounts X.1) V

theorem competition_timed_disabled_comparison (V C H : ℕ) (p : CompetitionRateBox) (hH : 1≤H) (hv : 0<(V:ℝ)) :
    (competitionDisabledCountKernel V C p hv).poissonized
      ((competitionClock V:ℝ≥0)*(500+(H:ℝ≥0)))
      (FiniteKernel.eventIndicator {X | competitionTimedDisabledPossible V C H X}) (foodInitial V,fun _=>0) ≤
      Real.exp (-(V:ℝ)*(H:ℝ)/25000)+
        resourcePotential V (boxCounts (foodInitial V))+(500+(H:ℝ))*(4*resourceSource V) := by
  let P := competitionDisabledCountKernel V C p hv
  let t : ℝ≥0 := 500+(H:ℝ≥0)
  let f := FiniteKernel.eventIndicator {X : BoxCounts V × CompetitionGrossCounters C | (V:ℝ)*(H:ℝ)/21000 < (competitionServiceCount 0 X.2:ℝ)}
  let g := FiniteKernel.eventIndicator {X : BoxCounts V | ¬resourceGood (boxCounts X) V}
  have hb (X : BoxCounts V × CompetitionGrossCounters C) :
      FiniteKernel.eventIndicator {Z | competitionTimedDisabledPossible V C H Z} X ≤ f X+g X.1 := by
    by_cases ha : (V:ℝ)*(H:ℝ)/21000 < (competitionServiceCount 0 X.2:ℝ)
    · by_cases hg : resourceGood (boxCounts X.1) V <;> simp [f,g,competitionTimedDisabledPossible,FiniteKernel.eventIndicator,ha,hg]
    · by_cases hg : resourceGood (boxCounts X.1) V <;> simp [f,g,competitionTimedDisabledPossible,FiniteKernel.eventIndicator,ha,hg]
  have hm := P.poissonized_mono ((competitionClock V:ℝ≥0)*t) _ (fun X=>f X+g X.1)
    (fun X=>(FiniteKernel.eventIndicator_bounds _ X).1)
    (fun X=>add_nonneg (FiniteKernel.eventIndicator_bounds _ X).1 (FiniteKernel.eventIndicator_bounds _ X.1).1) hb (foodInitial V,fun _=>0)
  rw [P.poissonized_add _ f (fun X=>g X.1)
    (fun X=>(FiniteKernel.eventIndicator_bounds _ X).1)
    (fun X=>(FiniteKernel.eventIndicator_bounds _ X.1).1)] at hm
  have hp := competition_counted_poisson C (competitionDisabledModel V p hv) competitionCreationLabel
    (competitionClock V) (by exact_mod_cast competitionClock_pos V hv) (competition_disabled_total V p hv)
    ((competitionClock V:ℝ≥0)*t) g (foodInitial V,fun _=>0)
  have hc := competition_timed_disabled_creation_probability V C H p hH hv
  have hr := competition_disabled_resource_probability V p hv t
  change P.poissonized ((competitionClock V:ℝ≥0)*t) (fun X=>g X.1) (foodInitial V,fun _=>0)=_ at hp
  rw [hp] at hm
  change P.poissonized ((competitionClock V:ℝ≥0)*t) f (foodInitial V,fun _=>0) ≤ _ at hc
  change _ ≤ resourcePotential V (boxCounts (foodInitial V))+(500+(H:ℝ))*(4*resourceSource V) at hr
  exact hm.trans (by linarith)


theorem competition_timed_disabled_cap (V H : ℕ) :
    (V:ℝ)*(H:ℝ)/21000 < (competitionTimedSupplyCap V 0 H:ℝ) := by
  have hc := competition_timed_supply_cap_strict V 0 H
  norm_num only [NNReal.coe_zero,add_zero] at hc
  have hn : 0≤(V:ℝ)*(H:ℝ) := by positivity
  have hv : 0≤(V:ℝ) := Nat.cast_nonneg _
  linarith

end
end RandomViability.Binding
