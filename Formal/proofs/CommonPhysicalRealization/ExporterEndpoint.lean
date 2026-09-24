import proofs.CommonPhysicalRealization.ExporterFamily
import proofs.RandomViability.BindingCompetitionPublication

namespace CommonPhysicalRealization
noncomputable section
open RandomViability.Binding FiniteCopy
open scoped BigOperators NNReal

/-- This endpoint concerns the literal donor finite marked kernels. The
unrestricted jump-process interpretation is a separately stated conventional proof. -/
theorem exporter_endpoint (p : physicalRectangle) (V : ℕ) (s : ℝ≥0) (m : ℕ)
    (hV : 0 < (V:ℝ)) :
    (∀ j e, (∑ i, pairLeft j i * composition i e) = ∑ i, pairRight j i * composition i e) ∧
    (∀ j, 0 < forwardCoefficient p.val.1 p.val.2 j ∧
      0 < reverseCoefficient p.val.1 p.val.2 j ∧
      Real.log (forwardCoefficient p.val.1 p.val.2 j / reverseCoefficient p.val.1 p.val.2 j) =
        ∑ i, ((pairLeft j i : ℝ)-pairRight j i)*standardPotential i) ∧
    (∀ N j, physicalRate N V p.val.1 p.val.2 1 1 j =
      competitionRate N V (1/500000000) (1/(donorParameters p).K)
        (donorParameters p).r (donorParameters p).delta j ∧
      physicalNext N j = competitionNext N j ∧
      physicalExport j = competitionExport j ∧
      ∀ q, physicalService q j = reservoirMark q j) ∧
    (∀ i, 0 < productiveDrift p.val.1 p.val.2 i) ∧
    1-competitionTimedRootError V s m ≤
      competitionTimedFullExpectation V s m (donorParameters p) hV
        (FiniteKernel.eventIndicator {X | competitionTimedFullGood V s m X}) := by
  exact ⟨material_balance, family_thermochemistry p,
    fun N j => marked_projection N V p.val.1 p.val.2 j,
    family_productive p, competition_timed_supplied_probability V s m (donorParameters p) hV⟩

/-- A fixed nonempty compact two-coordinate family, with no realization premise. -/
theorem common_physical_family :
    IsCompact physicalRectangle ∧ (20,3/100) ∈ physicalRectangle ∧
    (∀ p : physicalRectangle, ∀ V : ℕ, ∀ s : ℝ≥0, ∀ m : ℕ, ∀ hV : 0 < (V:ℝ),
      1-competitionTimedRootError V s m ≤
        competitionTimedFullExpectation V s m (donorParameters p) hV
          (FiniteKernel.eventIndicator {X | competitionTimedFullGood V s m X})) := by
  exact ⟨rectangle_compact,rectangle_interior_point,
    fun p V s m hV => (exporter_endpoint p V s m hV).2.2.2.2⟩

/-- Conservative rational confidence: the sharper inherited lower bound is
1 - 2 exp(-2), approximately 0.7293. -/
theorem worked_run (p : physicalRectangle) :
    (1/3:ℝ) ≤ competitionTimedFullExpectation 100000000 0 100 (donorParameters p)
      (by norm_num) (FiniteKernel.eventIndicator {X | competitionTimedFullGood 100000000 0 100 X}) := by
  have hd : (100:ℝ)+(0:ℝ≥0) ≤ competitionDuration 100000000 := by
    have hh := Real.add_one_le_exp (100:ℝ)
    norm_num [competitionDuration] at *
    linarith
  have h := competition_publication_probability 100000000 0 100 (donorParameters p)
    (by norm_num) (by norm_num) hd
  norm_num at h
  have h3 : (3:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
  have he : Real.exp (-2) ≤ (1/3:ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) h3
  linarith

theorem worked_supplies :
    2*(100000000:ℝ)*(500+100)=120000000000 ∧
    (100000000:ℝ)*(500+100)/8=7500000000 ∧
    (100000000:ℝ)/5000=20000 := by norm_num

end
end CommonPhysicalRealization
