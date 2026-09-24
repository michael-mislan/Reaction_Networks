import proofs.SmallCusp.Classification.StructuralEligibility
import proofs.SmallCusp.Equivalence.CodedSimple

namespace SmallCusp

def codedReactionSet (C : CodedBimolNetwork) : Finset BimolReactionCode :=
  Finset.univ.image C.reaction

theorem sameCodedReactionSet_iff_finset (C D : CodedBimolNetwork) :
    SameCodedReactionSet C D ↔ codedReactionSet C = codedReactionSet D := by
  classical
  simp only [SameCodedReactionSet, codedReactionSet]
  constructor
  · intro h
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    simpa only [Set.mem_range] using Set.ext_iff.mp h x
  · intro h
    ext x
    have hx := Finset.ext_iff.mp h x
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hx

theorem codedReactionSet_eq_cusp_iff (C D : CodedBimolNetwork)
    (h : codedReactionSet C = codedReactionSet D) :
    AdmitsTransverseCusp C.toNetwork ↔ AdmitsTransverseCusp D.toNetwork :=
  codedSimplyEquivalent_admitsTransverseCusp_iff
    (sameCodedReactionSet_implies_codedSimplyEquivalent
      ((sameCodedReactionSet_iff_finset C D).mpr h))

def sourceCross (e f : BimolReactionCode) : ℤ :=
  ((e.2.decode 0 : ℤ) - (e.1.decode 0 : ℤ)) *
      ((f.2.decode 1 : ℤ) - (f.1.decode 1 : ℤ)) -
    ((f.2.decode 0 : ℤ) - (f.1.decode 0 : ℤ)) *
      ((e.2.decode 1 : ℤ) - (e.1.decode 1 : ℤ))

def SourceRankTwo (S : Finset BimolReactionCode) : Prop :=
  ∃ e ∈ S, ∃ f ∈ S, sourceCross e f ≠ 0

def SourceKernelBalanced (S : Finset BimolReactionCode) : Prop :=
  ∀ e ∈ S,
    (e.1 ≠ e.2) →
      (∃ f ∈ S, sourceCross e f < 0) ∧
      (∃ f ∈ S, 0 < sourceCross e f)

def sourceReactantSupport (S : Finset BimolReactionCode) :
    Finset BimolComplexCode := S.image Prod.fst

def StructurallyEligibleSource (S : Finset BimolReactionCode) : Prop :=
  IsFiveReactionSourceCode S ∧ SourceRankTwo S ∧
    SourceKernelBalanced S ∧ 4 ≤ (sourceReactantSupport S).card

instance sourceRankTwo_decidable (S : Finset BimolReactionCode) :
    Decidable (SourceRankTwo S) := by unfold SourceRankTwo; infer_instance

instance sourceKernelBalanced_decidable (S : Finset BimolReactionCode) :
    Decidable (SourceKernelBalanced S) := by unfold SourceKernelBalanced; infer_instance

instance structurallyEligibleSource_decidable (S : Finset BimolReactionCode) :
    Decidable (StructurallyEligibleSource S) := by
  unfold StructurallyEligibleSource IsFiveReactionSourceCode
  infer_instance

@[simp] theorem sourceCross_coded (C : CodedBimolNetwork) (r s : Fin 5) :
    sourceCross (C.reaction r) (C.reaction s) = codedCross C r s := by
  rfl

theorem codedReactionSet_valid (C : CodedBimolNetwork) :
    IsFiveReactionSourceCode (codedReactionSet C) := by
  classical
  constructor
  · rw [codedReactionSet, Finset.card_image_of_injective]
    · simp
    · exact C.injective
  · intro e he
    rcases Finset.mem_image.mp he with ⟨r, _, rfl⟩
    exact C.noSelf r

theorem sourceRankTwo_coded (C : CodedBimolNetwork)
    (h : C.toNetwork.HasStoichiometricRankTwo) :
    SourceRankTwo (codedReactionSet C) := by
  rcases h with ⟨r, s, hrs⟩
  refine ⟨C.reaction r, ?_, C.reaction s, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
  · simpa [sourceCross, codedCross, codedStoich,
      CodedBimolNetwork.toNetwork, SmallPlanarNetwork.stoich] using hrs

theorem sourceKernelBalanced_coded (C : CodedBimolNetwork)
    (h : CodedKernelBalanced C) :
    SourceKernelBalanced (codedReactionSet C) := by
  intro e he hne
  rcases Finset.mem_image.mp he with ⟨r, _, rfl⟩
  have hr : codedStoich C 0 r ≠ 0 ∨ codedStoich C 1 r ≠ 0 := by
    by_contra hz
    simp only [not_or, not_not] at hz
    apply C.noSelf r
    apply BimolComplexCode.decode_injective
    funext i
    fin_cases i
    · have h0 := hz.1
      change ((C.reaction r).2.decode 0 : ℤ) -
          ((C.reaction r).1.decode 0 : ℤ) = 0 at h0
      have h0' := sub_eq_zero.mp h0
      exact_mod_cast h0'.symm
    · have h1 := hz.2
      change ((C.reaction r).2.decode 1 : ℤ) -
          ((C.reaction r).1.decode 1 : ℤ) = 0 at h1
      have h1' := sub_eq_zero.mp h1
      exact_mod_cast h1'.symm
  rcases h r hr with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  exact ⟨⟨C.reaction s, Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩,
      by simpa using hs⟩,
    ⟨C.reaction t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩,
      by simpa using ht⟩⟩

theorem sourceReactantSupport_coded (C : CodedBimolNetwork) :
    sourceReactantSupport (codedReactionSet C) = codedReactantSupport C := by
  classical
  ext c
  simp [sourceReactantSupport, codedReactionSet, codedReactantSupport]

theorem cusp_source_structurallyEligible (Q : SmallPlanarNetwork 5)
    (hQ : IsPlanarBimolecular252 Q) (hcusp : AdmitsTransverseCusp Q) :
    StructurallyEligibleSource
      (codedReactionSet (encodeBimolNetwork Q hQ.1 hQ.2.1)) := by
  let C := encodeBimolNetwork Q hQ.1 hQ.2.1
  have hnet : C.toNetwork = Q := encodeBimolNetwork_toNetwork Q hQ.1 hQ.2.1
  refine ⟨codedReactionSet_valid C, ?_, ?_, ?_⟩
  · apply sourceRankTwo_coded
    rw [hnet]
    exact hQ.2.2.1
  · exact sourceKernelBalanced_coded C
      (cusp_implies_codedKernelBalanced Q hQ hcusp)
  · rw [sourceReactantSupport_coded]
    exact bimolecular_cusp_requires_four_reactants Q hQ hcusp

end SmallCusp
