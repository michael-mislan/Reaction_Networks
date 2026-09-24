import proofs.RandomViability.JumpTrajectory
import proofs.RandomViability.UnboundedPhysicalStep

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

def physicalTrajectoryLaw (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) : Measure (ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :=
  jumpTrajectoryLaw N unboundedPhysicalNext (unboundedPhysicalRate c V D basal cat)
    (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat)

instance physicalTrajectoryLaw_probability (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) : IsProbabilityMeasure (physicalTrajectoryLaw hn c V D hV hD basal cat N) := by
  unfold physicalTrajectoryLaw
  infer_instance

theorem physicalTrajectoryLaw_transition (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (k : ℕ) :
    (physicalTrajectoryLaw hn c V D hV hD basal cat N).map (Preorder.frestrictLe k) ⊗ₘ
      jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V D basal cat)
        (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat) k =
    (physicalTrajectoryLaw hn c V D hV hD basal cat N).map
      (fun x => (Preorder.frestrictLe k x, x (k+1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end
end RandomViability

