import proofs.FiniteReservoir.PhysicalNonexplosion
import proofs.RandomViability.JumpPositiveRate

namespace FiniteReservoir
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding

/-- Every observed jump has positive literal propensity and the exact bath update. -/
theorem actual_source_events (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) (N : CountState M) :
    ∀ᵐ z ∂reactorTrajectory M p V hV N, ∀ k, ∃ j : CompetitionChannel,
      (z (k+1)).2.1=Sum.inr j ∧
      0 < rate (countState (z k).1) V p.release p.cleavage p.capacity j ∧
      (∀ i,reactants (competitionBase j) i ≤ (z k).1.1 i) ∧
      countState (z (k+1)).1=next (countState (z k).1) j := by
  have hs := jumpTrajectory_consistent N reactorNext (reactorRate M p V)
    (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV)
  have hp := jumpTrajectory_positive_rate N reactorNext (reactorRate M p V)
    (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV)
  filter_upwards [hs,hp] with z hz hpos
  intro k
  obtain ⟨j,hj,hn⟩ := hz k
  obtain ⟨l,hl,hpl⟩ := hpos k
  have hlj : l=j := Sum.inr.inj (hl.symm.trans hj)
  subst l
  have hne := ne_of_gt hpl
  refine ⟨j,hj,hpl,bath_internal_support (countState (z k).1) V p.release p.cleavage p.capacity j hne,?_⟩
  rw [hn]
  exact reactor_next_source M p V (z k).1 j hne

end
end FiniteReservoir
