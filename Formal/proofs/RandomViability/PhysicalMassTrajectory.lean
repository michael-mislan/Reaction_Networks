import proofs.RandomViability.JumpSupport
import proofs.RandomViability.PhysicalTrajectory
import proofs.RandomViability.JumpInitial
import proofs.RandomViability.CommonClock

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

def trajectoryFoodInput {n : ℕ} (label : Unit ⊕ PhysicalCountChannel n) : ℕ :=
  label.elim (fun _ => 0) foodInputMass

theorem unbounded_next_mass_input {n : ℕ} (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    countMass (unboundedPhysicalNext N ch) ≤ countMass N + foodInputMass ch := by
  unfold unboundedPhysicalNext
  split_ifs with he
  · exact physical_raw_mass_le_input N ch he
  · exact Nat.le_add_right _ _

theorem consistent_physical_mass_step {n : ℕ} (N : Molecule n → ℕ)
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (h : jumpConsistent unboundedPhysicalNext N y) :
    countMass y.1 ≤ countMass N + trajectoryFoodInput y.2.1 := by
  obtain ⟨ch, hm, hn⟩ := h
  rw [hm, hn]
  exact unbounded_next_mass_input N ch

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physicalTrajectory_mass_envelope (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    ∀ᵐ z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N, ∀ k,
      countMass (z k).1 ≤ countMass (z 0).1 +
        ∑ i ∈ Finset.range k, trajectoryFoodInput (z (i+1)).2.1 := by
  have hs := jumpTrajectory_consistent N unboundedPhysicalNext (unboundedPhysicalRate c V D basal cat)
    (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat)
  filter_upwards [hs] with z hz
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := consistent_physical_mass_step (z k).1 (z (k+1)) (hz k)
    rw [Finset.sum_range_succ]
    exact hstep.trans (by omega)

theorem physicalTrajectory_mass_from_initial (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    ∀ᵐ z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N, ∀ k,
      countMass (z k).1 ≤ countMass N +
        ∑ i ∈ Finset.range k, trajectoryFoodInput (z (i+1)).2.1 := by
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext (unboundedPhysicalRate c V D basal cat)
    (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat)
  filter_upwards [physicalTrajectory_mass_envelope hn c V D hV hD basal cat N, hi] with z hz hinit
  simpa only [hinit] using hz

omit [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)] in
theorem unbounded_rate_locally_bounded (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (B : ℕ) :
    ∃ q : NNReal, 1 ≤ (q : ℝ) ∧ ∀ N : Molecule n → ℕ, countMass N ≤ B →
      ∑ ch, unboundedPhysicalRate c V D basal cat N ch ≤ q := by
  let M := boundedPhysicalCountModel (B := B) c V D basal cat
  obtain ⟨q, hq, hb, _, _⟩ := three_model_clock_exists M M M
  refine ⟨q, hq, ?_⟩
  intro N hN
  let X : BoundedCounts n B := ⟨fun z => ⟨N z, by have hh := count_le_countMass N z; omega⟩, hN⟩
  exact hb X

theorem physicalTrajectory_local_rate_envelope (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (b : ℕ) :
    ∃ q : NNReal, 1 ≤ (q : ℝ) ∧
      ∀ᵐ z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N, ∀ k,
        (∑ i ∈ Finset.range k, trajectoryFoodInput (z (i+1)).2.1) ≤ b →
        ∑ ch, unboundedPhysicalRate c V D basal cat (z k).1 ch ≤ q := by
  obtain ⟨q, hq, hb⟩ := unbounded_rate_locally_bounded c V D basal cat (countMass N+b)
  refine ⟨q, hq, ?_⟩
  filter_upwards [physicalTrajectory_mass_from_initial hn c V D hV hD basal cat N] with z hz
  intro k hk
  exact hb (z k).1 ((hz k).trans (by omega))

end
end RandomViability
