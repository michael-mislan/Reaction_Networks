import proofs.LowFounderPrediction.Resolution
import proofs.InheritedCellAssay.PositiveTrajectory

namespace LowFounderPrediction.Minimality
noncomputable section
open Classical FiniteCopy FiniteCopyReactor CompositionalMemory MeasureTheory
open InheritedCellAssay
open scoped ENNReal

def reference : Rates where
  bS := 0
  dS := 3/10
  qS := 1/1000
  bR := 1/10
  dR := 0
  qR := 1/100000
  bS_nonneg := by norm_num
  dS_nonneg := by norm_num
  qS_nonneg := by norm_num
  bR_nonneg := by norm_num
  dR_nonneg := by norm_num
  qR_nonneg := by norm_num

theorem reference_admissible : RateBall reference := by norm_num [RateBall, reference]

def finiteSource : FiniteJumpModel (Fin 8) Bool where
  next := PositiveKilled.next
  rate n b := (10001/100000)*(PositiveTrajectory.finiteSource.rate n b)
  nonneg n b := mul_nonneg (by norm_num) (PositiveTrajectory.finiteSource.nonneg n b)

theorem finite_generator (g : Fin 8 → ℝ) (n : Fin 8) :
    finiteSource.generator g n = (10001/100000)*PositiveTrajectory.finiteSource.generator g n := by
  simp only [FiniteJumpModel.generator, finiteSource, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [PositiveTrajectory.finiteSource, PositiveKilled.source]
  ring

theorem finite_time_identity :
    finiteTimeExpectation finiteSource horizon PositiveTrajectory.payoff 0 =
      finiteTimeExpectation PositiveTrajectory.finiteSource CountThreshold.horizon
        PositiveTrajectory.payoff 0 := by
  have he : (horizon : ℝ) • jumpGeneratorMatrix finiteSource =
      (CountThreshold.horizon : ℝ) • jumpGeneratorMatrix PositiveTrajectory.finiteSource := by
    ext x y
    simp only [Matrix.smul_apply, smul_eq_mul, jumpGeneratorMatrix, finite_generator]
    change ((100000/10001)*Real.log 2)*((10001/100000)*_) = (Real.log 2)*_
    ring
  simp only [finiteTimeExpectation, he]

theorem live_bound (x : State) (hx : x ∈ PositiveTrajectory.live) :
    (∑ b, rate reference x b) ≤ 2 := by
  rw [total_eq, hx.1]
  have hr : (x.2 : ℝ) ≤ 7 := by exact_mod_cast hx.2.2
  norm_num [reference]
  linarith

theorem finite_bound (n : Fin 8) : finiteSource.total n ≤ 2 := by
  have hn : (n.val : ℝ) ≤ 7 := by exact_mod_cast (show n.val ≤ 7 by omega)
  simp [FiniteJumpModel.total, finiteSource, PositiveTrajectory.finiteSource,
    PositiveKilled.source]
  linarith

def stopped := stoppedClockKernel PositiveTrajectory.live next (rate reference)
  (rate_nonneg reference) 2 (by norm_num) live_bound

private theorem fin_seven (h : 7 < 8) : (⟨7,h⟩ : Fin 8) = 7 := rfl

set_option maxHeartbeats 600000 in
theorem step_projection (g : Fin 8 → ℝ) (x : State) :
    (∑ b, stopped.prob x b * g (PositiveTrajectory.observe (stopped.next x b))) =
      (finiteSource.uniformize 2 (by norm_num) finite_bound).step g (PositiveTrajectory.observe x) := by
  rw [FiniteJumpModel.uniformize_step]
  by_cases hx : x ∈ PositiveTrajectory.live
  · rcases x with ⟨s,r⟩
    have hs : s = 0 := hx.1
    have hl : 1 ≤ r := hx.2.1
    have hh : r ≤ 7 := hx.2.2
    subst s
    interval_cases r <;>
      norm_num [stopped, stoppedClockKernel, boundedClockKernel, stoppedRate,
        Fintype.sum_option, Fin.sum_univ_succ, PositiveTrajectory.live, next, rate, reference,
        PositiveTrajectory.observe, finiteSource, PositiveTrajectory.finiteSource,
        PositiveKilled.source, PositiveKilled.next, FiniteJumpModel.generator,
        fin_seven] <;> ring
  · simp [stopped, stoppedClockKernel, boundedClockKernel, stoppedRate, hx,
      Fintype.sum_option, PositiveTrajectory.observe, finiteSource,
      PositiveTrajectory.finiteSource, PositiveKilled.source, PositiveKilled.next,
      FiniteJumpModel.generator]

theorem finite_le_failure :
    ENNReal.ofReal (finiteTimeExpectation finiteSource horizon PositiveTrajectory.payoff 0) ≤
      chronologicalEndpoint next (rate reference) (rate_nonneg reference) (total_pos reference)
        PositiveTrajectory.failure (0,1) horizon := by
  have hp := clock_finite_projection stopped finiteSource PositiveTrajectory.observe (2 : NNReal)
    horizon (by norm_num) finite_bound step_projection PositiveTrajectory.payoff
    PositiveTrajectory.payoff_bounds (0,1)
  have ho : PositiveTrajectory.observe (0,1) = 0 := by
    norm_num [PositiveTrajectory.observe, PositiveTrajectory.live]
  rw [ho] at hp
  have hc : causalClockEndpoint stopped 2
      (fun y => if y ∈ PositiveTrajectory.live then PositiveTrajectory.failure y else 0)
      (0,1) horizon =
      ENNReal.ofReal (finiteTimeExpectation finiteSource horizon PositiveTrajectory.payoff 0) := by
    unfold causalClockEndpoint
    split_ifs with ht
    · simpa only [PositiveTrajectory.observed_payoff] using hp
    · exact (ht horizon.property).elim
  rw [← hc]
  exact stopped_clock_le_unrestricted PositiveTrajectory.live next (rate reference)
    (rate_nonneg reference) (total_pos reference) 2 (by norm_num) live_bound
    PositiveTrajectory.failure (fun x => by unfold PositiveTrajectory.failure; split_ifs <;> norm_num)
    (0,1) horizon

def failureSet : Set State := {x | 3 ≤ x.1+x.2}

theorem failure_probability :
    chronologicalEndpoint next (rate reference) (rate_nonneg reference) (total_pos reference)
      PositiveTrajectory.failure (0,1) horizon = law reference (0,1) horizon failureSet := by
  rw [chronological_endpoint_measure next (rate reference) (rate_nonneg reference)
    (total_pos reference) (0,1) horizon horizon.property (source_nonexplosion reference (0,1))]
  have hf : PositiveTrajectory.failure = failureSet.indicator (fun _ => 1) := by
    funext y
    simp [PositiveTrajectory.failure, failureSet, Set.indicator]
  rw [hf, lintegral_indicator (Set.to_countable _).measurableSet]
  simp [law]

theorem reference_failure_gt :
    (1/20 : ℝ) < (oneFounder reference (5/24)).real failureSet := by
  have h := finite_le_failure
  rw [finite_time_identity, failure_probability] at h
  have hr := (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp h
  have hf := PositiveKilled.finite_failure_gt
  have hmix : (oneFounder reference (5/24)).real failureSet =
      (19/24)*(law reference (1,0) horizon).real failureSet+
      (5/24)*(law reference (0,1) horizon).real failureSet := by
    unfold oneFounder
    rw [measureReal_add_apply]
    norm_num
  rw [hmix]
  have hs : 0 ≤ (law reference (1,0) horizon).real failureSet := measureReal_nonneg
  change finiteTimeExpectation PositiveTrajectory.finiteSource CountThreshold.horizon
    PositiveTrajectory.payoff 0 ≤ (law reference (0,1) horizon).real failureSet at hr
  change (1/20 : ℝ) < (5/24)*finiteTimeExpectation PositiveTrajectory.finiteSource
    CountThreshold.horizon PositiveTrajectory.payoff 0 at hf
  linarith

instance reference_probability : IsProbabilityMeasure (oneFounder reference (5/24)) where
  measure_univ := by
    simp [oneFounder, Measure.add_apply, Measure.smul_apply]
    change ENNReal.ofReal (1-5/24 : ℝ)+ENNReal.ofReal (5/24 : ℝ) = 1
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num

theorem reference_two_undercovers :
    (oneFounder reference (5/24)).real {x | x.1+x.2 ≤ 2} < (19/20 : ℝ) := by
  have he : {x : State | x.1+x.2 ≤ 2} = failureSetᶜ := by
    ext x
    simp only [failureSet, Set.mem_compl_iff, Set.mem_setOf_eq]
    omega
  rw [he, probReal_compl_eq_one_sub (Set.to_countable failureSet).measurableSet]
  linarith [reference_failure_gt]

theorem no_lower_endpoint (k : ℕ) (hk : k ≤ 2) :
    (oneFounder reference (5/24)).real {x | x.1+x.2 ≤ k} < (19/20 : ℝ) := by
  have hm : (oneFounder reference (5/24)).real {x | x.1+x.2 ≤ k} ≤
      (oneFounder reference (5/24)).real {x | x.1+x.2 ≤ 2} := by
    exact measureReal_mono (fun x hx => le_trans hx hk) (by finiteness)
  exact hm.trans_lt reference_two_undercovers

end
end LowFounderPrediction.Minimality
