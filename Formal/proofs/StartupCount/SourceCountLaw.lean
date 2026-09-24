import proofs.StartupCount.PhysicalAffineBound
import proofs.StartupCount.PowerGenerator
import proofs.RandomViability.PhysicalTrajectory
import proofs.StartupCount.TerminalEvent

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000

def countGuard {n : ℕ} (V : NNReal) (r : Reaction n) (N : Molecule n → ℕ) : Prop :=
  (countMass N : ℝ) ≤ 11*V ∧ foodFloor*V ≤ (N (reactionLeft r) : ℝ) ∧
    foodFloor*V ≤ (N (reactionRight r) : ℝ)

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- The fixed-time count-tilt bound under the literal chemical trajectory law.
The guard is retained in the payoff, not assumed to hold almost surely. -/
theorem source_count_terminal_bound (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hbas : (1/500000000 : ℝ) ≤ basal r)
    (m : ℕ) (hm : 10 ≤ m) (hmV : (m : ℝ) ≤ (V : ℝ)/2000000000000000000)
    (T : ℝ) (hT : 0 ≤ T) (N₀ : Molecule n → ℕ) :
    (∫⁻ z,⨆ k,killedTerminal (countGuard V r)
      (fun N => ENNReal.ofReal ((9/10 : ℝ)^(N (reactionProduct r)))) k T z
      ∂physicalTrajectoryLaw hn cfg V 1 hV (by norm_num) basal cat N₀) ≤
      ENNReal.ofReal (affineEnvelope ((V : ℝ)/100000000000000000)
        (((1558/9)*(m : ℝ)*(9/10 : ℝ)^m)/((V : ℝ)/100000000000000000))
        ((9/10 : ℝ)^(N₀ (reactionProduct r))) T) := by
  apply physical_affine_terminal_bound unboundedPhysicalNext (unboundedPhysicalRate cfg V 1 basal cat)
    (unboundedPhysicalRate_nonneg cfg V 1 basal cat)
    (unbounded_total_pos hn cfg V 1 hV (by norm_num) basal cat)
    (countGuard V r) (fun N => (9/10 : ℝ)^(N (reactionProduct r))) (fun _ => by positivity)
    ((V : ℝ)/100000000000000000)
    (((1558/9)*(m : ℝ)*(9/10 : ℝ)^m)/((V : ℝ)/100000000000000000))
    (by positivity) (by positivity) _ _ T hT N₀
  · intro N _
    exact source_clock_dominates hn cfg V hV basal cat N
  · intro N hN
    have hh := physical_power_affine_generator cfg V hV basal cat N r hb hc hfood hN.1 hlen
      huw huz hwz hbas hN.2.1 hN.2.2 m hm hmV
    have he : ((V : ℝ)/100000000000000000)*
        (((1558/9)*(m : ℝ)*(9/10 : ℝ)^m)/((V : ℝ)/100000000000000000)) =
        (1558/9)*(m : ℝ)*(9/10 : ℝ)^m := by
      field_simp
    rwa [he]

theorem source_count_low_event_bound (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hbas : (1/500000000 : ℝ) ≤ basal r)
    (m : ℕ) (hm : 10 ≤ m) (hmV : (m : ℝ) ≤ (V : ℝ)/2000000000000000000)
    (T : ℝ) (hT : 0 ≤ T) (N₀ : Molecule n → ℕ) (h : ℕ) :
    ENNReal.ofReal ((9/10 : ℝ)^h)*
      physicalTrajectoryLaw hn cfg V 1 hV (by norm_num) basal cat N₀
        (guardedLowEvent (countGuard V r) (fun N => N (reactionProduct r)) h T) ≤
      ENNReal.ofReal (affineEnvelope ((V : ℝ)/100000000000000000)
        (((1558/9)*(m : ℝ)*(9/10 : ℝ)^m)/((V : ℝ)/100000000000000000))
        ((9/10 : ℝ)^(N₀ (reactionProduct r))) T) := by
  exact (guardedLowEvent_weighted_bound
    (physicalTrajectoryLaw hn cfg V 1 hV (by norm_num) basal cat N₀)
    (countGuard V r) (fun N => N (reactionProduct r)) h T).trans
      (source_count_terminal_bound hn cfg V hV basal cat r hb hc hfood hlen huw huz hwz
        hbas m hm hmV T hT N₀)

end
end StartupCount
