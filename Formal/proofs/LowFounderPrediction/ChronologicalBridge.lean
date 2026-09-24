import proofs.LowFounderPrediction.HistoryCertificate
import proofs.FiniteCopyReactor.EndpointMeasure
import proofs.CompositionalMemory.JumpNonexplosion

namespace LowFounderPrediction
noncomputable section
open Classical FiniteCopy FiniteCopyReactor CompositionalMemory MeasureTheory RandomViability Filter
open scoped ENNReal

def success (x : State) : ℝ≥0∞ := if x.1+x.2 ≤ 3 then 1 else 0

theorem success_le_one (x : State) : success x ≤ 1 := by
  unfold success
  split_ifs <;> norm_num

theorem observed_payoff (x : State) :
    ENNReal.ofReal (payoff (observe x)) = if x ∈ live then success x else 0 := by
  by_cases hx : x ∈ live
  · have he := repr_observe x hx
    have ho : (observe x).val ≠ 5 := fun h => hx (Fin.ext h)
    have hc : x.1+x.2 ≤ 3 := by
      rw [← he]
      generalize observe x = n at *
      fin_cases n <;> norm_num [repr] at *
    simp [payoff, hx, ho, success, hc]
  · have ho : observe x = 5 := by simpa [live] using hx
    simp [payoff, hx, ho]

theorem finite_le_actual (a : Rates) (T : NNReal) (x : State) :
    ENNReal.ofReal (finiteTimeExpectation (killed a) T payoff (observe x)) ≤
      chronologicalEndpoint next (rate a) (rate_nonneg a) (total_pos a) success x T := by
  let q : NNReal := ⟨clockRate a, (clock_pos a).le⟩
  have hp := InheritedCellAssay.clock_finite_projection (stopped a) (killed a) observe q T
    (clock_pos a) (killed_bound a) (step_projection a) payoff payoff_bounds x
  have hc : causalClockEndpoint (stopped a) (clockRate a)
      (fun y => if y ∈ live then success y else 0) x T =
      ENNReal.ofReal (finiteTimeExpectation (killed a) T payoff (observe x)) := by
    unfold causalClockEndpoint
    split_ifs with ht
    · simpa only [observed_payoff] using hp
    · exact (ht T.property).elim
  rw [← hc]
  exact stopped_clock_le_unrestricted live next (rate a) (rate_nonneg a) (total_pos a)
    (clockRate a) (clock_pos a) (live_bound a) success success_le_one x T

def population (x : State) : ℝ := (x.1 : ℝ)+x.2+1

theorem population_pos (x : State) : 0 < population x := by unfold population; positivity

theorem population_drift (a : Rates) (x : State) :
    (∑ b, rate a x b*(population (next x b)-population x)) ≤
      (a.bS+a.bR)*population x := by
  have hbS := a.bS_nonneg; have hdS := a.dS_nonneg; have hqS := a.qS_nonneg
  have hbR := a.bR_nonneg; have hdR := a.dR_nonneg; have hqR := a.qR_nonneg
  rcases x with ⟨s,r⟩
  cases s <;> cases r <;>
    simp [Fin.sum_univ_succ, rate, next, population, Nat.cast_add, Nat.cast_one] <;>
    nlinarith

theorem local_rate_bound (a : Rates) (B : ℕ) : ∃ q : ℝ, 0 < q ∧
    ∀ x, population x ≤ B → (∑ b, rate a x b) ≤ q := by
  let k := a.bS+a.dS+a.qS+a.bR+a.dR+a.qR
  have hbS := a.bS_nonneg; have hdS := a.dS_nonneg; have hqS := a.qS_nonneg
  have hbR := a.bR_nonneg; have hdR := a.dR_nonneg; have hqR := a.qR_nonneg
  have hk : 0 ≤ k := by dsimp [k]; positivity
  refine ⟨k*B+1, by positivity, ?_⟩
  intro x hx
  have hs : 0 ≤ (x.1 : ℝ) := by positivity
  have hr : 0 ≤ (x.2 : ℝ) := by positivity
  have hsB : (x.1 : ℝ) ≤ B := by unfold population at hx; linarith
  have hrB : (x.2 : ℝ) ≤ B := by unfold population at hx; linarith
  have hsum : (x.1 : ℝ)+x.2 ≤ B := by unfold population at hx; linarith
  have hm := mul_le_mul_of_nonneg_left hsum hk
  rw [total_eq]
  dsimp [k] at hm
  nlinarith

theorem source_nonexplosion (a : Rates) (x : State) :
    ∀ᵐ z ∂jumpTrajectoryLaw x next (rate a) (rate_nonneg a) (total_pos a),
      Tendsto (jumpElapsed z) atTop atTop :=
  jump_times_diverge x next (rate a) (rate_nonneg a) (total_pos a) population population_pos
    (a.bS+a.bR) (add_nonneg a.bS_nonneg a.bR_nonneg) (population_drift a) (local_rate_bound a)

def law (a : Rates) (x : State) (T : NNReal) : Measure State :=
  chronologicalMeasure next (rate a) (rate_nonneg a) (total_pos a) x T

instance law_probability (a : Rates) (x : State) (T : NNReal) :
    IsProbabilityMeasure (law a x T) := by unfold law; infer_instance

theorem endpoint_probability (a : Rates) (x : State) (T : NNReal) :
    chronologicalEndpoint next (rate a) (rate_nonneg a) (total_pos a) success x T =
      law a x T {y | y.1+y.2 ≤ 3} := by
  rw [chronological_endpoint_measure next (rate a) (rate_nonneg a) (total_pos a) x T
    T.property (source_nonexplosion a x)]
  have hf : success = Set.indicator {y : State | y.1+y.2 ≤ 3} (fun _ => 1) := by
    funext y
    simp [success, Set.indicator]
  rw [hf, lintegral_indicator (Set.to_countable _).measurableSet]
  simp [law]

theorem source_lower (a : Rates) (ha : Admissible a) (T : NNReal) (x : State) :
    ENNReal.ofReal (value T (observe x)) ≤ law a x T {y | y.1+y.2 ≤ 3} := by
  have h := (ENNReal.ofReal_le_ofReal (finite_lower a ha T (observe x))).trans
    (finite_le_actual a T x)
  simpa only [endpoint_probability] using h

end
end LowFounderPrediction
