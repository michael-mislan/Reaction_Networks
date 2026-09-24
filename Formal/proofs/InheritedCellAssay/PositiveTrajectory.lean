import proofs.InheritedCellAssay.FiniteClockProjection
import proofs.InheritedCellAssay.PositiveKilled
import proofs.FiniteCopyReactor.StoppedAgreement

namespace InheritedCellAssay.PositiveTrajectory
noncomputable section
open Classical FiniteCopy FiniteCopyReactor CompositionalMemory
open scoped ENNReal

abbrev State := ℕ × ℕ

/-- Sensitive and resistant counts. Labels: R birth, R-to-S, S death,
    S-to-R, and a silent clock tick. Time is scaled by 10001/100000 per day.
    The last label ensures a positive total clock even at extinction. -/
def next (x : State) (b : Fin 5) : State :=
  if b.val = 0 then (x.1, x.2+1)
  else if b.val = 1 then (x.1+1, x.2-1)
  else if b.val = 2 then (x.1-1, x.2)
  else if b.val = 3 then (x.1-1, x.2+1)
  else x

def rate (x : State) (b : Fin 5) : ℝ :=
  if b.val = 0 then (10000/10001)*x.2
  else if b.val = 1 then (1/10001)*x.2
  else if b.val = 2 then (30000/10001)*x.1
  else if b.val = 3 then (100/10001)*x.1
  else 1

theorem rate_nonneg (x : State) (b : Fin 5) : 0 ≤ rate x b := by
  unfold rate
  split_ifs <;> positivity

theorem total_eq (x : State) : (∑ b, rate x b) = x.2 + (30100/10001)*x.1 + 1 := by
  simp [Fin.sum_univ_succ, rate]
  ring

theorem total_pos (x : State) : 0 < ∑ b, rate x b := by
  rw [total_eq]
  positivity

def live : Set State := {x | x.1 = 0 ∧ 1 ≤ x.2 ∧ x.2 ≤ 7}

theorem live_bound (x : State) (hx : x ∈ live) : (∑ b, rate x b) ≤ 8 := by
  rw [total_eq, hx.1]
  have h : (x.2 : ℝ) ≤ 7 := by exact_mod_cast hx.2.2
  linarith

def observe (x : State) : Fin 8 :=
  if hx : x ∈ live then ⟨x.2-1, by have := hx.2.2; omega⟩ else 7

def finiteSource := PositiveKilled.source (10000/10001) (by norm_num) (by norm_num)

theorem finite_bound (n : Fin 8) : finiteSource.total n ≤ 8 := by
  have h : (n.val : ℝ) ≤ 7 := by exact_mod_cast (show n.val ≤ 7 by omega)
  simp [finiteSource, FiniteJumpModel.total, PositiveKilled.source]
  linarith

def stopped := stoppedClockKernel live next rate rate_nonneg 8 (by norm_num) live_bound

private theorem fin_seven (h : 7 < 8) : (⟨7,h⟩ : Fin 8) = 7 := rfl

/-- The exact stopped process has the same observed transition as the finite
    killed model; zero-rate labels and silent events are included explicitly. -/
theorem step_projection (g : Fin 8 → ℝ) (x : State) :
    (∑ b, stopped.prob x b * g (observe (stopped.next x b))) =
      (finiteSource.uniformize 8 (by norm_num) finite_bound).step g (observe x) := by
  rw [FiniteJumpModel.uniformize_step]
  by_cases hx : x ∈ live
  · rcases x with ⟨s,r⟩
    have hs : s = 0 := hx.1
    have hlow : 1 ≤ r := hx.2.1
    have hhigh : r ≤ 7 := hx.2.2
    subst s
    interval_cases r <;>
      norm_num [stopped, stoppedClockKernel, boundedClockKernel, stoppedRate,
        Fintype.sum_option, Fin.sum_univ_succ, live, next, rate, observe,
        finiteSource, PositiveKilled.source, PositiveKilled.next, FiniteJumpModel.generator,
        fin_seven] <;> ring
  · simp [stopped, stoppedClockKernel, boundedClockKernel, stoppedRate, hx,
      Fintype.sum_option, observe, finiteSource, PositiveKilled.source,
      PositiveKilled.next, FiniteJumpModel.generator]

def payoff (n : Fin 8) : ℝ := if 2 ≤ n.val ∧ n.val ≤ 6 then 1 else 0

theorem payoff_bounds (n : Fin 8) : 0 ≤ payoff n ∧ payoff n ≤ 1 := by
  unfold payoff
  split_ifs <;> norm_num

def failure (x : State) : ℝ≥0∞ := if 3 ≤ x.1+x.2 then 1 else 0

theorem observed_payoff (x : State) :
    ENNReal.ofReal (payoff (observe x)) = if x ∈ live then failure x else 0 := by
  by_cases hx : x ∈ live
  · have hs := hx.1
    have hl := hx.2.1
    have hh := hx.2.2
    simp only [observe, dif_pos hx, payoff, Fin.val_mk, if_pos hx, failure, hs, zero_add]
    by_cases h3 : 3 ≤ x.2
    · have he : 2 ≤ x.2-1 ∧ x.2-1 ≤ 6 := by omega
      simp [he, h3]
    · have he : ¬ (2 ≤ x.2-1 ∧ x.2-1 ≤ 6) := by omega
      simp only [if_neg he, ENNReal.ofReal_zero, if_neg h3]
  · norm_num [observe, hx, payoff]

theorem finite_le_actual :
    ENNReal.ofReal (finiteTimeExpectation finiteSource CountThreshold.horizon payoff 0) ≤
      chronologicalEndpoint next rate rate_nonneg total_pos failure (0,1)
        CountThreshold.horizon := by
  have hp := clock_finite_projection stopped finiteSource observe (8 : NNReal)
    CountThreshold.horizon (by norm_num) finite_bound step_projection payoff payoff_bounds (0,1)
  have ho : observe (0,1) = 0 := by norm_num [observe, live]
  rw [ho] at hp
  have hc : causalClockEndpoint stopped 8
      (fun y => if y ∈ live then failure y else 0) (0,1) CountThreshold.horizon =
      ENNReal.ofReal (finiteTimeExpectation finiteSource CountThreshold.horizon payoff 0) := by
    unfold causalClockEndpoint
    split_ifs with ht
    · simpa only [observed_payoff] using hp
    · exact (ht CountThreshold.horizon.property).elim
  rw [← hc]
  exact stopped_clock_le_unrestricted live next rate rate_nonneg total_pos 8
    (by norm_num) live_bound failure (fun x => by unfold failure; split_ifs <;> norm_num) (0,1) _

/-- True trajectory failure for the stated initial mixture exceeds five percent.
    Sensitive-founder histories contribute a nonnegative additional term. -/
def mixtureFailure : ℝ≥0∞ :=
  ENNReal.ofReal (19/24 : ℝ) *
    chronologicalEndpoint next rate rate_nonneg total_pos failure (1,0) CountThreshold.horizon +
  ENNReal.ofReal (5/24 : ℝ) *
    chronologicalEndpoint next rate rate_nonneg total_pos failure (0,1) CountThreshold.horizon

theorem actual_failure_gt : ENNReal.ofReal (1/20 : ℝ) < mixtureFailure := by
  have hf := PositiveKilled.finite_failure_gt
  change (1/20 : ℝ) < (5/24)*finiteTimeExpectation finiteSource CountThreshold.horizon payoff 0 at hf
  have hh : ENNReal.ofReal (1/20 : ℝ) <
      ENNReal.ofReal ((5/24)*finiteTimeExpectation finiteSource CountThreshold.horizon payoff 0) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hf
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5/24)] at hh
  exact (hh.trans_le (mul_le_mul_right finite_le_actual _)).trans_le (le_add_left le_rfl)

end
end InheritedCellAssay.PositiveTrajectory
