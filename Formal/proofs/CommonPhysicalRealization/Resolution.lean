import proofs.CommonPhysicalRealization.ExporterEndpoint
import proofs.CommonPhysicalRealization.ResidentCompletion
import proofs.CommonPhysicalRealization.Supplies

namespace CommonPhysicalRealization
noncomputable section
open RandomViability.Binding FiniteCopy
open scoped BigOperators NNReal

/-- Source-instantiated finite-law C0 endpoint, with literal chemistry and its
coefficient/propensity bridge. No physical-realizability premise is assumed.
The companion and unrestricted-process proof boundaries are stated in the report. -/
theorem resolution :
    IsCompact physicalRectangle ∧ (20,3/100) ∈ physicalRectangle ∧
    (∀ j e, (∑ i, pairLeft j i*composition i e) = ∑ i, pairRight j i*composition i e) ∧
    (∀ p : physicalRectangle,
      (∀ j, 0 < forwardCoefficient p.val.1 p.val.2 j ∧
        0 < reverseCoefficient p.val.1 p.val.2 j ∧
        Real.log (forwardCoefficient p.val.1 p.val.2 j / reverseCoefficient p.val.1 p.val.2 j) =
          ∑ i, ((pairLeft j i:ℝ)-pairRight j i)*standardPotential i) ∧
      (∀ N V aF aP j,
        physicalRate N V p.val.1 p.val.2 aF aP (pairForward j) =
          forwardCoefficient p.val.1 p.val.2 j*forwardSubstrate N V aF j ∧
        physicalRate N V p.val.1 p.val.2 aF aP (pairReverse j) =
          reverseCoefficient p.val.1 p.val.2 j*reverseSubstrate N V aP j) ∧
      (∀ N V j, physicalRate N V p.val.1 p.val.2 1 1 j =
        competitionRate N V (1/500000000) (1/10) p.val.1 p.val.2 j ∧
        physicalNext N j = competitionNext N j ∧ physicalExport j = competitionExport j ∧
        ∀ q, physicalService q j = reservoirMark q j) ∧
      (∀ i, 0 < productiveDrift p.val.1 p.val.2 i) ∧
      (1/3:ℝ) ≤ competitionTimedFullExpectation 100000000 0 100 (donorParameters p)
        (by norm_num) (FiniteKernel.eventIndicator {X | competitionTimedFullGood 100000000 0 100 X})) := by
  refine ⟨rectangle_compact,rectangle_interior_point,material_balance,?_⟩
  intro p
  exact ⟨family_thermochemistry p,
    fun N V aF aP j => coefficient_binding N V p.val.1 p.val.2 aF aP j,
    fun N V j => marked_projection N V p.val.1 p.val.2 j,
    family_productive p,worked_run p⟩

end
end CommonPhysicalRealization
