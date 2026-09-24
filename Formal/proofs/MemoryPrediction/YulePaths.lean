import proofs.MemoryPrediction.Aggregation
import proofs.LowFounderPrediction.ChronologicalBridge
import proofs.RandomViability.JumpSupport
import proofs.RandomViability.JumpPositiveRate
import proofs.RandomViability.JumpInitial

namespace MemoryPrediction
noncomputable section
open Classical LowFounderPrediction RandomViability FiniteCopyReactor MeasureTheory
open scoped ENNReal

/-- Normalized time: fast division rate one, dormant S, no deaths or switching. -/
def yuleRates : Rates where
  bS := 0
  dS := 0
  qS := 0
  bR := 1
  dR := 0
  qR := 0
  bS_nonneg := by norm_num
  dS_nonneg := by norm_num
  qS_nonneg := by norm_num
  bR_nonneg := by norm_num
  dR_nonneg := by norm_num
  qR_nonneg := by norm_num

theorem yule_supported_step (x : State) (b : Fin 7) (hb : 0 < rate yuleRates x b) :
    (next x b).1 = x.1 ∧ x.2 ≤ (next x b).2 := by
  fin_cases b <;> norm_num [rate, next, yuleRates] at *

theorem yule_path_structure (x : State) :
    ∀ᵐ z ∂jumpTrajectoryLaw x next (rate yuleRates) (rate_nonneg yuleRates) (total_pos yuleRates),
      (∀ n, (z n).1.1 = x.1) ∧ Monotone (fun n => (z n).1.2) := by
  filter_upwards [jumpTrajectory_consistent x next (rate yuleRates)
      (rate_nonneg yuleRates) (total_pos yuleRates),
    jumpTrajectory_positive_rate x next (rate yuleRates)
      (rate_nonneg yuleRates) (total_pos yuleRates),
    jumpTrajectory_initial_population x next (rate yuleRates)
      (rate_nonneg yuleRates) (total_pos yuleRates)] with z hz hp hzero
  have hstep (n : ℕ) : (z (n+1)).1.1=(z n).1.1 ∧ (z n).1.2 ≤ (z (n+1)).1.2 := by
    obtain ⟨b,hb,hnext⟩ := hz n
    obtain ⟨c,hc,hpos⟩ := hp n
    have he : c=b := Sum.inr.inj (hc.symm.trans hb)
    subst c
    rw [hnext]
    exact yule_supported_step _ b hpos
  constructor
  · intro n
    induction n with
    | zero => exact congrArg Prod.fst hzero
    | succ n ih => exact (hstep n).1.trans ih
  · exact monotone_nat_of_le_succ (fun n => (hstep n).2)

def yuleLive (s : ℕ) : Set State := {x | x.1=s ∧ x.2 ≤ 7}
def countSuccess (k : ℕ) (x : State) : ℝ≥0∞ := if totalCount x ≤ k then 1 else 0

/-- Killing above seven R cells loses no successful history for the stated
threshold. This source fact removes the need for a truncation-error campaign. -/
theorem yule_killed_exact (x : State) (k : ℕ) (hk : k ≤ x.1+7) (T : ℝ) :
    killedChronologicalEndpoint (yuleLive x.1) next (rate yuleRates)
      (rate_nonneg yuleRates) (total_pos yuleRates) (countSuccess k) x T =
    chronologicalEndpoint next (rate yuleRates)
      (rate_nonneg yuleRates) (total_pos yuleRates) (countSuccess k) x T := by
  apply lintegral_congr_ae
  filter_upwards [yule_path_structure x] with z hz
  unfold killedEndpointObservable endpointObservable
  apply tsum_congr
  intro n
  by_cases ht : jumpElapsed z n ≤ T ∧ T < jumpElapsed z (n+1)
  · simp only [ht, true_and, if_true]
    by_cases hs : totalCount (z n).1 ≤ k
    · have ha : prefixAlive (yuleLive x.1) n z := by
        intro i hi
        refine ⟨hz.1 i, ?_⟩
        have hm := hz.2 hi
        change (z i).1.2 ≤ (z n).1.2 at hm
        have he := hz.1 n
        unfold totalCount at hs
        omega
      simp [ha]
    · simp [countSuccess, hs]
  · simp only [ht, false_and, if_false]

end
end MemoryPrediction
