import proofs.RandomViability.ProductiveOperationProbability

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

theorem disabled_catalytic_rate_zero {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (basal : Reaction n → NNReal) (N : Molecule n → ℕ)
    (r : Reaction n) (x : Molecule n) (d : Bool) :
    unboundedPhysicalRate c V D basal (fun _ _ => 0) N (.inr (.inr (r,x,d))) = 0 := by
  simp [unboundedPhysicalRate,physicalChannelRate,physicalChannelCoefficient]

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Same basal chemistry, food feed, initialization and observation window;
disabling catalytic acceleration makes positive signed catalytic operation
impossible under the actual full trajectory law. -/
theorem catalyst_disabled_operation_zero (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (N : Molecule n → ℕ)
    (r : Reaction n) (v m : ℕ) (hm : 0 < m) :
    physicalTrajectoryLaw hn c V D hV hD basal (fun _ _ => 0) N
      {z | ProductiveOperation r v m z} = 0 := by
  have hp := jumpTrajectory_positive_rate N unboundedPhysicalNext
    (unboundedPhysicalRate c V D basal (fun _ _ => 0))
    (unboundedPhysicalRate_nonneg c V D basal (fun _ _ => 0))
    (unbounded_total_pos hn c V D hV hD basal (fun _ _ => 0))
  have hnone : ∀ᵐ z ∂physicalTrajectoryLaw hn c V D hV hD basal (fun _ _ => 0) N,
      ¬ ProductiveOperation r v m z := by
    filter_upwards [hp] with z hz hoper
    obtain ⟨i,s,x,d,_,htag⟩ := productive_operation_firing r v m hm z hoper
    obtain ⟨b,hb,hr⟩ := hz i
    have he : b = .inr (.inr (s,x,d)) := Sum.inr.inj (hb.symm.trans htag)
    rw [he,disabled_catalytic_rate_zero] at hr
    exact (lt_irrefl (0 : ℝ)) hr
  simpa only [not_not] using ae_iff.mp hnone

end
end RandomViability
