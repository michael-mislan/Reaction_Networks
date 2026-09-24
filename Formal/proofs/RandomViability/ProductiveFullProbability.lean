import proofs.RandomViability.ProductiveKineticMarks
import proofs.RandomViability.ProductiveRAFProbability

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Probability under independent uniform S,B,H marks, the complete source
law, and all physical reaction clocks, with the declared food-only start. -/
def fullyAveragedProductiveProbability (hn : 4 ≤ n) (V : ℕ) (hV : 40 ≤ V) (a : ℝ) : ℝ :=
  uniformFiniteAverage (fun u : KineticMarkConfig n =>
    sourceAverage a n (fun c =>
      (physicalTrajectoryLaw (by omega) c (V : NNReal) 1
        (by exact_mod_cast (show 0 < V by omega)) (by norm_num)
        (kineticBasal u) (kineticCatalytic u) (foodOnlyCounts n V)
        {z | ProductiveRAFSuccess c (productiveReaction hn) V ((V+9)/10) z}).toReal))

/-- All environmental and trajectory randomness is averaged explicitly.
The theorem gives a finite-size result; a joint-limit conclusion is separate. -/
theorem fully_averaged_productive_bounds (hn : 4 ≤ n) (V : ℕ) (hV : 40 ≤ V)
    (a : ℝ) (ha : 1 < a) :
    productiveBeta V*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ≤
      fullyAveragedProductiveProbability hn V hV a ∧
    fullyAveragedProductiveProbability hn V hV a ≤
      (Fintype.card (Molecule (10*V))*Fintype.card (Reaction (10*V+2)) : ℕ)*
        (windowZipfMean a (sourceReactionCount n)/sourceReactionCount n) := by
  apply uniform_finite_average_bounds
  intro u
  exact source_productive_raf_bounds hn V hV a ha (kineticBasal u) (kineticCatalytic u)
    (kinetic_basal_bounds u) (kinetic_catalytic_bounds u)

end
end RandomViability
