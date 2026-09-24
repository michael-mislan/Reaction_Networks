import proofs.FiniteCopyReactor.CountNonexplosion
import proofs.RandomViability.JumpPositiveRate

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding

/-- Simultaneously at every jump, the observed event has positive literal
propensity and the next population is the literal physical update. -/
theorem actual_source_events (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (N : Counts) :
    ∀ᵐ z ∂reactorTrajectory V r d hV hr hd N, ∀ k, ∃ j : CompetitionChannel,
      (z (k+1)).2.1=Sum.inr j ∧
      0 < CommonPhysicalRealization.physicalRate (z k).1 V r d 1 1 j ∧
      (∀ i,reactants (competitionBase j) i ≤ (z k).1 i) ∧
      (z (k+1)).1=CommonPhysicalRealization.physicalNext (z k).1 j := by
  have hs := jumpTrajectory_consistent N reactorNext (reactorRate V r d)
    (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd)
  have hp := jumpTrajectory_positive_rate N reactorNext (reactorRate V r d)
    (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd)
  filter_upwards [hs,hp] with z hz hpos
  intro k
  obtain ⟨j,hj,hn⟩ := hz k
  obtain ⟨l,hl,hpl⟩ := hpos k
  have hlj : l=j := Sum.inr.inj (hl.symm.trans hj)
  subst l
  have hne := ne_of_gt hpl
  refine ⟨j,hj,?_,competition_rate_support _ V _ _ r d j hne,?_⟩
  · rw [CommonPhysicalRealization.rate_projection]
    exact hpl
  · rw [hn,reactor_next_source _ V r d j hne]

end
end FiniteCopyReactor
