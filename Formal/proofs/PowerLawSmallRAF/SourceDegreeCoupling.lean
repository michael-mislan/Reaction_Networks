import proofs.PowerLawSmallRAF.RowDegreeMixture
import proofs.PowerLawSmallRAF.SourceSmallRAFUnionBound

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev SourceDegreeConfig (n : Nat) := Molecule n → Fin (Fintype.card (Reaction n) + 1)

theorem source_boundedRevRAF_event_mono {n m : Nat}
    (B T : SourceMoleculeFibreConfig n) (hsub : ∀ x, B x ⊆ T x)
    (hB : ∃ S : Finset (Reaction n), S.card ≤ m ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig B) S) :
    ∃ S : Finset (Reaction n), S.card ≤ m ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig T) S := by
  obtain ⟨S, hcard, hne, hfood, hcat⟩ := hB
  refine ⟨S, hcard, hne, hfood, ?_⟩
  intro r hr
  obtain ⟨x, k, hx, hxr⟩ := hcat r hr
  exact ⟨x, k, hx, hsub x hxr⟩

/-- Source-faithful small-RAF transfer. Auxiliary probabilities may depend on
the entire degree vector. The exact tail pays no error for inactive rows. -/
theorem sourceBoundedRevRAFProbability_ge_degree_coupling
    (a : ℝ) (n m : Nat) (ha : 1 < a)
    (p : SourceDegreeConfig n → Molecule n → ℝ)
    (hp : ∀ d x, 0 ≤ p d x) (hp1 : ∀ d x, p d x ≤ 1) :
    (∑ d : SourceDegreeConfig n,
      (∏ x, cappedZipfDegreeMass a (sourceReactionCount n) (d x)) *
      ∑ B : SourceMoleculeFibreConfig n,
        if ∃ S : Finset (Reaction n), S.card ≤ m ∧
          IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig B) S
        then bernoulliRowsWeight (p d) B else 0) ≤
      sourceBoundedRevRAFProbability a n m +
      ∑ d : SourceDegreeConfig n,
        (∏ x, cappedZipfDegreeMass a (sourceReactionCount n) (d x)) *
        ∑ x, bernoulliRowOverflowMass (J := Reaction n) (p d x) (d x) := by
  classical
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have h := bernoulliRows_degree_mixture_event_le
    (fun (_ : Molecule n) d => cappedZipfDegreeMass a (sourceReactionCount n) d)
    (fun _ d => cappedZipfDegreeMass_nonneg a _ d hzpos) p hp hp1
    (fun B : SourceMoleculeFibreConfig n => ∃ S : Finset (Reaction n), S.card ≤ m ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig B) S)
    (fun B T hsub hB => source_boundedRevRAF_event_mono B T hsub hB)
  simpa only [sourceBoundedRevRAFProbability, sourcePowerLawConfigWeight] using h

end
end PowerLawSmallRAF
