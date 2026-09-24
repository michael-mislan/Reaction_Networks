import proofs.RandomViability.BindingCompetitionDisabledProbability
import proofs.RandomViability.BindingCompetitionCounterHistory

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

def competitionDisabledPossible (V C : ℕ) (X : BoxCounts V × CompetitionGrossCounters C) : Prop :=
  (V:ℝ)*(competitionWindowNumber V:ℝ)/21000 < (competitionServiceCount 0 X.2:ℝ) ∨
    ¬resourceGood (boxCounts X.1) V

theorem competition_disabled_comparison (V C : ℕ) (p : CompetitionRateBox) (hV : 100000000≤V) (hv : 0<(V:ℝ)) :
    (competitionDisabledCountKernel V C p hv).poissonized
      ((competitionClock V:ℝ≥0)*(500+⟨competitionDuration V,(Real.exp_pos _).le⟩))
      (FiniteKernel.eventIndicator {X | competitionDisabledPossible V C X}) (foodInitial V,fun _=>0) ≤
      Real.exp (-(V:ℝ)*(competitionWindowNumber V:ℝ)/25000)+
        resourcePotential V (boxCounts (foodInitial V))+(500+competitionDuration V)*(4*resourceSource V) := by
  let P := competitionDisabledCountKernel V C p hv
  let t : ℝ≥0 := 500+⟨competitionDuration V,(Real.exp_pos _).le⟩
  let f := FiniteKernel.eventIndicator {X : BoxCounts V × CompetitionGrossCounters C | (V:ℝ)*(competitionWindowNumber V:ℝ)/21000 < (competitionServiceCount 0 X.2:ℝ)}
  let g := FiniteKernel.eventIndicator {X : BoxCounts V | ¬resourceGood (boxCounts X) V}
  have hb (X : BoxCounts V × CompetitionGrossCounters C) :
      FiniteKernel.eventIndicator {Z | competitionDisabledPossible V C Z} X ≤ f X+g X.1 := by
    by_cases ha : (V:ℝ)*(competitionWindowNumber V:ℝ)/21000 < (competitionServiceCount 0 X.2:ℝ)
    · by_cases hg : resourceGood (boxCounts X.1) V <;> simp [f,g,competitionDisabledPossible,FiniteKernel.eventIndicator,ha,hg]
    · by_cases hg : resourceGood (boxCounts X.1) V <;> simp [f,g,competitionDisabledPossible,FiniteKernel.eventIndicator,ha,hg]
  have hm := P.poissonized_mono ((competitionClock V:ℝ≥0)*t) _ (fun X=>f X+g X.1)
    (fun X=>(FiniteKernel.eventIndicator_bounds _ X).1)
    (fun X=>add_nonneg (FiniteKernel.eventIndicator_bounds _ X).1 (FiniteKernel.eventIndicator_bounds _ X.1).1) hb (foodInitial V,fun _=>0)
  rw [P.poissonized_add _ f (fun X=>g X.1)
    (fun X=>(FiniteKernel.eventIndicator_bounds _ X).1)
    (fun X=>(FiniteKernel.eventIndicator_bounds _ X.1).1)] at hm
  have hp := competition_counted_poisson C (competitionDisabledModel V p hv) competitionCreationLabel
    (competitionClock V) (by exact_mod_cast competitionClock_pos V hv) (competition_disabled_total V p hv)
    ((competitionClock V:ℝ≥0)*t) g (foodInitial V,fun _=>0)
  have hc := competition_disabled_creation_probability V C p hV hv
  have hr := competition_disabled_resource_probability V p hv t
  change P.poissonized ((competitionClock V:ℝ≥0)*t) (fun X=>g X.1) (foodInitial V,fun _=>0)=_ at hp
  rw [hp] at hm
  change P.poissonized ((competitionClock V:ℝ≥0)*t) f (foodInitial V,fun _=>0) ≤ _ at hc
  change _ ≤ resourcePotential V (boxCounts (foodInitial V))+(500+competitionDuration V)*(4*resourceSource V) at hr
  exact hm.trans (by linarith)

theorem competition_disabled_threshold_below_cap (V : ℕ) :
    (V:ℝ)*(competitionWindowNumber V:ℝ)/21000 < (competitionSupplyCap V:ℝ) := by
  have hc := competition_supply_cap_strict V
  have hm : (competitionWindowNumber V:ℝ) ≤ competitionDuration V := Nat.floor_le (Real.exp_pos _).le
  have hh := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) V)
  have hn : 0≤(V:ℝ)*(competitionDuration V) := by unfold competitionDuration; positivity
  have hv : 0≤(V:ℝ) := Nat.cast_nonneg _
  linarith

end
end RandomViability.Binding
