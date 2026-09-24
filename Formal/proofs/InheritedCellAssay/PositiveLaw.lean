import proofs.InheritedCellAssay.PositiveTrajectory
import proofs.CompositionalMemory.JumpNonexplosion
import proofs.FiniteCopyReactor.EndpointMeasure

namespace InheritedCellAssay.PositiveTrajectory
noncomputable section
open Classical CompositionalMemory FiniteCopyReactor RandomViability MeasureTheory Filter
open scoped ENNReal

def population (x : State) : ℝ := (x.1 : ℝ)+x.2+1

theorem population_positive (x : State) : 0 < population x := by
  unfold population
  positivity

theorem population_drift (x : State) :
    (∑ b, rate x b*(population (next x b)-population x)) ≤ 1*population x := by
  rcases x with ⟨s,r⟩
  cases s <;> cases r <;>
    simp [Fin.sum_univ_succ, rate, next, population, Nat.cast_add, Nat.cast_one] <;>
    nlinarith

theorem local_rate_bound (B : ℕ) : ∃ q : ℝ, 0 < q ∧
    ∀ x, population x ≤ B → (∑ b, rate x b) ≤ q := by
  refine ⟨4*B+1, by positivity, ?_⟩
  intro x hx
  rw [total_eq]
  unfold population at hx
  have hs : 0 ≤ (x.1 : ℝ) := by positivity
  have hr : 0 ≤ (x.2 : ℝ) := by positivity
  linarith

theorem source_nonexplosion (x : State) :
    ∀ᵐ z ∂jumpTrajectoryLaw x next rate rate_nonneg total_pos,
      Tendsto (jumpElapsed z) atTop atTop :=
  jump_times_diverge x next rate rate_nonneg total_pos population population_positive 1
    (by norm_num) population_drift local_rate_bound

def countFailureSet : Set State := {x | 3 ≤ x.1+x.2}

theorem failure_eq_probability (x : State) :
    chronologicalEndpoint next rate rate_nonneg total_pos failure x CountThreshold.horizon =
      chronologicalMeasure next rate rate_nonneg total_pos x CountThreshold.horizon countFailureSet := by
  rw [chronological_endpoint_measure next rate rate_nonneg total_pos x
    CountThreshold.horizon CountThreshold.horizon.property (source_nonexplosion x)]
  have hf : failure = countFailureSet.indicator (fun _ => 1) := by
    funext y
    simp [failure, countFailureSet, Set.indicator]
  rw [hf]
  rw [lintegral_indicator (Set.to_countable countFailureSet).measurableSet]
  simp

/-- A statement about actual probabilities under a normalized, nonexplosive
    source law, rather than a possibly subprobabilistic chronology observable. -/
theorem actual_count_probability_gt : ENNReal.ofReal (1/20 : ℝ) <
    ENNReal.ofReal (19/24 : ℝ) *
      chronologicalMeasure next rate rate_nonneg total_pos (1,0) CountThreshold.horizon countFailureSet +
    ENNReal.ofReal (5/24 : ℝ) *
      chronologicalMeasure next rate rate_nonneg total_pos (0,1) CountThreshold.horizon countFailureSet := by
  simpa only [mixtureFailure, failure_eq_probability] using actual_failure_gt

end
end InheritedCellAssay.PositiveTrajectory
