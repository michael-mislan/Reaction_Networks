import proofs.MemoryPrediction.Aggregation
import proofs.MemoryPrediction.ScalarKilled
import proofs.MemoryPrediction.ClockComparison
import proofs.LowFounderPrediction.ChronologicalBridge

namespace MemoryPrediction
noncomputable section
open Classical FiniteCopy FiniteCopyReactor CompositionalMemory LowFounderPrediction
open MeasureTheory
open scoped ENNReal

def capCount (n : ℕ) : Fin 7 := ⟨min n 6, by omega⟩
def countProjection (x : State) : Fin 7 := capCount (totalCount x)
def countLive : Set State := {x | totalCount x ≤ 5}

def comparisonClock (a : Rates) : ℝ := 2+5*(a.bS+a.dS+a.qS+a.bR+a.dR+a.qR)

theorem comparisonClock_ge_one (a : Rates) : 1 ≤ comparisonClock a := by
  have := a.bS_nonneg; have := a.dS_nonneg; have := a.qS_nonneg
  have := a.bR_nonneg; have := a.dR_nonneg; have := a.qR_nonneg
  unfold comparisonClock
  linarith

theorem comparisonClock_pos (a : Rates) : 0 < comparisonClock a := by
  linarith [comparisonClock_ge_one a]

theorem comparisonClock_bound (a : Rates) (x : State) (hx : x ∈ countLive) :
    (∑ e, rate a x e) ≤ comparisonClock a := by
  have := a.bS_nonneg; have := a.dS_nonneg; have := a.qS_nonneg
  have := a.bR_nonneg; have := a.dR_nonneg; have := a.qR_nonneg
  have hs : (x.1 : ℝ) ≤ 5 := by exact_mod_cast (show x.1 ≤ 5 by exact le_trans (Nat.le_add_right _ _) hx)
  have hr : (x.2 : ℝ) ≤ 5 := by exact_mod_cast (show x.2 ≤ 5 by exact le_trans (Nat.le_add_left _ _) hx)
  rw [total_eq]
  unfold comparisonClock
  nlinarith

def comparisonStopped (a : Rates) :=
  stoppedClockKernel countLive next (rate a) (rate_nonneg a) (comparisonClock a)
    (comparisonClock_pos a) (comparisonClock_bound a)

theorem cap_antitone (g : Fin 7 → ℝ) (hg : Antitone g) :
    Antitone (fun n => g (capCount n)) := by
  intro i j hij
  exact hg (show capCount i ≤ capCount j from min_le_min_right 6 hij)

theorem scalar_generator_lift (g : Fin 7 → ℝ) (n : ℕ) (hn : n ≤ 5) :
    scalarKilled.generator g (capCount n) =
      (501/5000)*(n : ℝ)*(g (capCount (n+1))-g (capCount n)) +
      (1/20)*(n : ℝ)*(g (capCount (n-1))-g (capCount n)) := by
  interval_cases n <;> norm_num [FiniteJumpModel.generator, scalarKilled, capCount]

theorem stopped_step_inside (a : Rates) (w : State → ℝ) (x : State) (hx : x ∈ countLive) :
    (∑ e, (comparisonStopped a).prob x e * w ((comparisonStopped a).next x e)) =
      w x + (∑ e, rate a x e*(w (next x e)-w x))/comparisonClock a := by
  simp only [comparisonStopped, stoppedClockKernel, boundedClockKernel, stoppedRate,
    if_pos hx, Fintype.sum_option]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem source_step_lower (a : Rates)
    (hbS : a.bS ≤ 501/5000) (hbR : a.bR ≤ 501/5000)
    (hdS : 1/20 ≤ a.dS) (hdR : 1/20 ≤ a.dR)
    (g : Fin 7 → ℝ) (hg : decreasingKilled g) (x : State) :
    (scalarKilled.uniformize (comparisonClock a) (comparisonClock_pos a)
      (fun n => (scalar_total_bound n).trans (comparisonClock_ge_one a))).step g
        (countProjection x) ≤
      ∑ e, (comparisonStopped a).prob x e * g (countProjection ((comparisonStopped a).next x e)) := by
  by_cases hx : x ∈ countLive
  · rw [stopped_step_inside a (fun y => g (countProjection y)) x hx,
      FiniteJumpModel.uniformize_step]
    apply add_le_add (le_refl _)
    apply div_le_div_of_nonneg_right _ (comparisonClock_pos a).le
    change scalarKilled.generator g (capCount (totalCount x)) ≤ _
    rw [scalar_generator_lift g _ hx]
    exact count_generator_lower a (501/5000) (1/20) hbS hbR hdS hdR
      (fun n => g (capCount n)) (cap_antitone g hg.1) x
  · have hp : countProjection x = 6 := by
      apply Fin.ext
      simp only [countProjection, capCount]
      have : 6 ≤ totalCount x := by
        have hh : ¬totalCount x ≤ 5 := hx
        omega
      exact min_eq_right this
    rw [FiniteJumpModel.uniformize_step, hp]
    simp [FiniteJumpModel.generator, scalarKilled, comparisonStopped,
      stoppedClockKernel, boundedClockKernel, stoppedRate, hx, Fintype.sum_option, hp]

/-- Uniform source-connected lower bound, with no switching-rate restriction
other than the finite nonnegative rates carried by Rates. -/
theorem source_scalar_lower (a : Rates)
    (hbS : a.bS ≤ 501/5000) (hbR : a.bR ≤ 501/5000)
    (hdS : 1/20 ≤ a.dS) (hdR : 1/20 ≤ a.dR)
    (T : NNReal) (x : State) :
    ENNReal.ofReal (finiteTimeExpectation scalarKilled T scalarPayoff (countProjection x)) ≤
      law a x T {y | totalCount y ≤ 4} := by
  let q : NNReal := ⟨comparisonClock a, (comparisonClock_pos a).le⟩
  have hp := clock_finite_lower (comparisonStopped a) scalarKilled countProjection q T
    (comparisonClock_pos a) (fun n => (scalar_total_bound n).trans (comparisonClock_ge_one a))
    decreasingKilled (scalar_preserves _ (comparisonClock_ge_one a) _)
    (source_step_lower a hbS hbR hdS hdR) scalarPayoff scalarPayoff_decreasing
    (fun n => by unfold scalarPayoff; split_ifs <;> norm_num) x
  let f : State → ℝ≥0∞ := fun y => if totalCount y ≤ 4 then 1 else 0
  have hf : ∀ y, f y ≤ 1 := by intro y; dsimp [f]; split_ifs <;> norm_num
  have he : (fun y => ENNReal.ofReal (scalarPayoff (countProjection y))) =
      (fun y => if y ∈ countLive then f y else 0) := by
    funext y
    simp only [scalarPayoff, countProjection, capCount, countLive, Set.mem_setOf_eq]
    dsimp [f]
    split_ifs <;> norm_num at * <;> omega
  rw [he] at hp
  have hc := stopped_clock_le_unrestricted countLive next (rate a) (rate_nonneg a)
    (total_pos a) (comparisonClock a) (comparisonClock_pos a) (comparisonClock_bound a) f hf x T
  have hcp : clockEndpoint (comparisonStopped a) q T
      (fun y => if y ∈ countLive then f y else 0) x ≤
      chronologicalEndpoint next (rate a) (rate_nonneg a) (total_pos a) f x T := by
    simpa [causalClockEndpoint, comparisonStopped, q] using hc
  have h := hp.trans hcp
  rw [chronological_endpoint_measure next (rate a) (rate_nonneg a) (total_pos a)
    x T T.property (source_nonexplosion a x)] at h
  have hfind : f = Set.indicator {y : State | totalCount y ≤ 4} (fun _ => 1) := by
    funext y
    simp [f, Set.indicator]
  rw [hfind, lintegral_indicator (Set.to_countable _).measurableSet] at h
  simpa [law] using h

end
end MemoryPrediction
