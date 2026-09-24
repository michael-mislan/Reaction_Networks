import proofs.SmallCusp.Classification.BimolecularClassification
import proofs.SmallCusp.Classification.SourceCatalogueCount
import proofs.SmallCusp.Obstruction.FewReactantObstruction

namespace SmallCusp

/-- Every literal planar bimolecular `(2,5,2)` cusp uses at least four
distinct reactant complexes. -/
theorem four_reactants_necessary_for_bimolecular_cusp
    (Q : SmallPlanarNetwork 5) (hQ : IsPlanarBimolecular252 Q)
    (hcusp : AdmitsTransverseCusp Q) :
    4 ≤ (codedReactantSupport
      (encodeBimolNetwork Q hQ.1 hQ.2.1)).card :=
  bimolecular_cusp_requires_four_reactants Q hQ hcusp

/-- A literal five-reaction bimolecular cusp with five distinct reactants. -/
theorem five_distinct_reactants_suffice :
    ∃ C : CodedBimolNetwork,
      (codedReactantSupport C).card = 5 ∧
      AdmitsTransverseCusp C.toNetwork := by
  refine ⟨positiveCusp0, ?_, positiveCusp0_admitsTransverseCusp⟩
  native_decide

/-- Cusp existence forces the positive kernel-balance geometry used by the
source classifier. -/
theorem balanced_generator_necessary_for_bimolecular_cusp
    (Q : SmallPlanarNetwork 5) (hQ : IsPlanarBimolecular252 Q)
    (hcusp : AdmitsTransverseCusp Q) :
    CodedKernelBalanced (encodeBimolNetwork Q hQ.1 hQ.2.1) :=
  cusp_implies_codedKernelBalanced Q hQ hcusp

theorem bimolecular_cusp_class_count :
    bimolecularCuspClasses.length = 52 :=
  bimolecularCuspClasses_length

theorem obstruction_filtration_exhaustive_count :
    bimolecularCuspClasses.length +
      conicDeterminantLayerRecords.length +
      circuitFoldLayerRecords.length +
      cubicResidualLayerRecords.length = 9999 :=
  bimolecularMechanismClass_partition_count

/-- The finite reductions used by the public classification: literal eligible
sources, species-swap representatives, simple-equivalence mechanisms, and
positive cusp mechanisms. -/
theorem bimolecular_quotient_compression_counts :
    structurallyEligibleSourceCatalogue.card = 60036 ∧
    sourceCoverageRecords.length = 30051 ∧
    bimolecularCuspClasses.length +
      conicDeterminantLayerRecords.length +
      circuitFoldLayerRecords.length +
      cubicResidualLayerRecords.length = 9999 ∧
    bimolecularCuspClasses.length = 52 := by
  exact ⟨structurallyEligibleSourceCatalogue_card,
    sourceCoverageRecords_length,
    bimolecularMechanismClass_partition_count,
    bimolecularCuspClasses_length⟩

/-- Five reactions suffice for a literal planar bimolecular cusp. -/
theorem five_reaction_bimolecular_cusp_exists :
    ∃ Q : SmallPlanarNetwork 5,
      IsPlanarBimolecular252 Q ∧ AdmitsTransverseCusp Q := by
  refine ⟨positiveCusp0.toNetwork, ?_,
    positiveCusp0_admitsTransverseCusp⟩
  native_decide

end SmallCusp
