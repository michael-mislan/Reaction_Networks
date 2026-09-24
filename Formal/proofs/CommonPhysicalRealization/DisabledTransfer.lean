import proofs.CommonPhysicalRealization.ExporterEndpoint

namespace CommonPhysicalRealization
noncomputable section
open RandomViability.Binding FiniteCopy
open scoped BigOperators NNReal

def physicalDisabledRate (N : Counts) (V r d : ℝ) (j : CompetitionChannel) : ℝ :=
  if j=Sum.inl 6 ∨ j=Sum.inl 7 then 0 else physicalRate N V r d 1 1 j

theorem disabled_source_projection (N : Counts) (V r d : ℝ) (j : CompetitionChannel) :
    physicalDisabledRate N V r d j = competitionDisabledRate N V (1/500000000) (1/10) r d j := by
  unfold physicalDisabledRate
  rw [rate_projection]
  cases j with
  | inl j => simp [competitionDisabledRate,competitionRate,disabledRate]
  | inr j => simp [competitionDisabledRate,competitionRate]

theorem disabled_preserves_driving (N : Counts) (V r d : ℝ) (j : Fin 2) :
    physicalDisabledRate N V r d (.inr j) = physicalRate N V r d 1 1 (.inr j) := by
  simp [physicalDisabledRate]

/-- Deletion removes a pair, never imposes zero coefficients on retained chemistry. -/
theorem retained_chemistry (p : physicalRectangle) (j : {j : Fin 6 // j≠3}) :
    (∀ e, (∑ i,pairLeft j.val i*composition i e)=∑ i,pairRight j.val i*composition i e) ∧
    (0 < forwardCoefficient p.val.1 p.val.2 j.val ∧
      0 < reverseCoefficient p.val.1 p.val.2 j.val ∧
      Real.log (forwardCoefficient p.val.1 p.val.2 j.val / reverseCoefficient p.val.1 p.val.2 j.val) =
        ∑ i,((pairLeft j.val i:ℝ)-pairRight j.val i)*standardPotential i) := by
  exact ⟨material_balance j.val,family_thermochemistry p j.val⟩

theorem realized_disabled_comparison (V C H : ℕ) (p : physicalRectangle)
    (hH : 1≤H) (hv : 0<(V:ℝ)) :
    (competitionDisabledCountKernel V C (donorParameters p) hv).poissonized
      ((competitionClock V:ℝ≥0)*(500+(H:ℝ≥0)))
      (FiniteKernel.eventIndicator {X | competitionTimedDisabledPossible V C H X}) (foodInitial V,fun _=>0) ≤
      Real.exp (-(V:ℝ)*(H:ℝ)/25000)+
        resourcePotential V (boxCounts (foodInitial V))+(500+(H:ℝ))*(4*resourceSource V) :=
  competition_timed_disabled_comparison V C H (donorParameters p) hH hv

end
end CommonPhysicalRealization
