import proofs.SmallCusp.Source.SourceClasses

/-!
# A complete finite source catalogue for bimolecular `(2,5,2)` networks

There are six two-species complexes of molecularity at most two.  This file
encodes them, forms the finite universe of directed non-self reactions, and
proves that every literal bimolecular five-reaction source has a five-element
representative in the catalogue, canonical up to swapping the two species.
-/

open scoped BigOperators

namespace SmallCusp

inductive BimolComplexCode where
  | zero | x | y | xx | xy | yy
  deriving DecidableEq, Fintype, Repr

def BimolComplexCode.decode : BimolComplexCode → Complex
  | .zero => ![0, 0]
  | .x    => ![1, 0]
  | .y    => ![0, 1]
  | .xx   => ![2, 0]
  | .xy   => ![1, 1]
  | .yy   => ![0, 2]

def BimolComplexCode.swap : BimolComplexCode → BimolComplexCode
  | .zero => .zero
  | .x    => .y
  | .y    => .x
  | .xx   => .yy
  | .xy   => .xy
  | .yy   => .xx

def BimolComplexCode.index : BimolComplexCode → ℕ
  | .zero => 0 | .x => 1 | .y => 2 | .xx => 3 | .xy => 4 | .yy => 5

@[simp] theorem BimolComplexCode.swap_swap (c : BimolComplexCode) :
    c.swap.swap = c := by cases c <;> rfl

theorem BimolComplexCode.swap_injective : Function.Injective BimolComplexCode.swap := by
  intro a b h
  simpa only [BimolComplexCode.swap_swap] using congrArg BimolComplexCode.swap h

theorem exists_bimolComplexCode (z : Complex) (hz : molecularity z ≤ 2) :
    ∃ c : BimolComplexCode, c.decode = z := by
  have hsum : z 0 + z 1 ≤ 2 := by
    simpa [molecularity, Fin.sum_univ_succ] using hz
  have h0le : z 0 ≤ 2 := by omega
  have h1le : z 1 ≤ 2 := by omega
  interval_cases h0 : z 0 <;> interval_cases h1 : z 1
  · exact ⟨.zero, by funext i; fin_cases i <;> simp [BimolComplexCode.decode, h0, h1]⟩
  · exact ⟨.y, by funext i; fin_cases i <;> simp [BimolComplexCode.decode, h0, h1]⟩
  · exact ⟨.yy, by funext i; fin_cases i <;> simp [BimolComplexCode.decode, h0, h1]⟩
  · exact ⟨.x, by funext i; fin_cases i <;> simp [BimolComplexCode.decode, h0, h1]⟩
  · exact ⟨.xy, by funext i; fin_cases i <;> simp [BimolComplexCode.decode, h0, h1]⟩
  · omega
  · exact ⟨.xx, by funext i; fin_cases i <;> simp [BimolComplexCode.decode, h0, h1]⟩
  · omega
  · omega

noncomputable def encodeBimolComplex (z : Complex) : BimolComplexCode :=
  if hz : molecularity z ≤ 2 then Classical.choose (exists_bimolComplexCode z hz)
  else .zero

theorem decode_encodeBimolComplex (z : Complex) (hz : molecularity z ≤ 2) :
    (encodeBimolComplex z).decode = z := by
  rw [encodeBimolComplex, dif_pos hz]
  exact Classical.choose_spec (exists_bimolComplexCode z hz)

abbrev BimolReactionCode := BimolComplexCode × BimolComplexCode

def swapBimolReaction (e : BimolReactionCode) : BimolReactionCode :=
  (e.1.swap, e.2.swap)

@[simp] theorem swapBimolReaction_swap (e : BimolReactionCode) :
    swapBimolReaction (swapBimolReaction e) = e := by
  rcases e with ⟨a, b⟩
  simp [swapBimolReaction]

theorem swapBimolReaction_injective : Function.Injective swapBimolReaction := by
  intro a b h
  simpa only [swapBimolReaction_swap] using congrArg swapBimolReaction h

def swapBimolReactionSet (S : Finset BimolReactionCode) : Finset BimolReactionCode :=
  S.image swapBimolReaction

@[simp] theorem swapBimolReactionSet_swap (S : Finset BimolReactionCode) :
    swapBimolReactionSet (swapBimolReactionSet S) = S := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨d, hd, rfl⟩
    rcases Finset.mem_image.mp hd with ⟨c, hc, rfl⟩
    simpa using hc
  · intro he
    apply Finset.mem_image.mpr
    refine ⟨swapBimolReaction e, ?_, by simp⟩
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩

def bimolReactionIndex (e : BimolReactionCode) : ℕ :=
  6 * e.1.index + e.2.index

def bimolCatalogueKey (S : Finset BimolReactionCode) : ℕ :=
  ∑ e ∈ S, 2 ^ bimolReactionIndex e

def IsFiveReactionSourceCode (S : Finset BimolReactionCode) : Prop :=
  S.card = 5 ∧ ∀ e ∈ S, e.1 ≠ e.2

def IsSpeciesSwapCanonical (S : Finset BimolReactionCode) : Prop :=
  bimolCatalogueKey S ≤ bimolCatalogueKey (swapBimolReactionSet S)

noncomputable def bimolecular252Catalogue : Finset (Finset BimolReactionCode) := by
  classical
  exact Finset.univ.filter fun S =>
    IsFiveReactionSourceCode S ∧ IsSpeciesSwapCanonical S

noncomputable def encodedReactionSet (Q : SmallPlanarNetwork 5) : Finset BimolReactionCode :=
  Finset.univ.image fun r : Fin 5 =>
    (encodeBimolComplex (Q.reactant r), encodeBimolComplex (Q.product r))

theorem encodedReactionSet_card (Q : SmallPlanarNetwork 5)
    (hr : Q.ReactantsAtMost 2) (hp : Q.ProductsAtMost 2) :
    (encodedReactionSet Q).card = 5 := by
  classical
  rw [encodedReactionSet, Finset.card_image_of_injective]
  · simp
  · intro r s hrs
    apply Q.reactionInjective
    apply Prod.ext
    · simpa [decode_encodeBimolComplex (Q.reactant r) (hr r),
        decode_encodeBimolComplex (Q.reactant s) (hr s)] using
        congrArg (fun e : BimolReactionCode => e.1.decode) hrs
    · simpa [decode_encodeBimolComplex (Q.product r) (hp r),
        decode_encodeBimolComplex (Q.product s) (hp s)] using
        congrArg (fun e : BimolReactionCode => e.2.decode) hrs

theorem encodedReactionSet_noSelf (Q : SmallPlanarNetwork 5)
    (hr : Q.ReactantsAtMost 2) (hp : Q.ProductsAtMost 2) :
    ∀ e ∈ encodedReactionSet Q, e.1 ≠ e.2 := by
  classical
  intro e he heq
  rw [encodedReactionSet, Finset.mem_image] at he
  rcases he with ⟨r, -, rfl⟩
  apply Q.noSelfReaction r
  calc
    Q.reactant r = (encodeBimolComplex (Q.reactant r)).decode :=
      (decode_encodeBimolComplex _ (hr r)).symm
    _ = (encodeBimolComplex (Q.product r)).decode := congrArg BimolComplexCode.decode heq
    _ = Q.product r := decode_encodeBimolComplex _ (hp r)

theorem encodedReactionSet_valid (Q : SmallPlanarNetwork 5)
    (hr : Q.ReactantsAtMost 2) (hp : Q.ProductsAtMost 2) :
    IsFiveReactionSourceCode (encodedReactionSet Q) :=
  ⟨encodedReactionSet_card Q hr hp, encodedReactionSet_noSelf Q hr hp⟩

theorem swapBimolReactionSet_valid {S : Finset BimolReactionCode}
    (hS : IsFiveReactionSourceCode S) :
    IsFiveReactionSourceCode (swapBimolReactionSet S) := by
  classical
  constructor
  · rw [swapBimolReactionSet, Finset.card_image_of_injective _ swapBimolReaction_injective]
    exact hS.1
  · intro e he heq
    rw [swapBimolReactionSet, Finset.mem_image] at he
    rcases he with ⟨d, hd, rfl⟩
    apply hS.2 d hd
    apply BimolComplexCode.swap_injective
    exact heq

theorem sourceCode_or_swap_isCanonical (S : Finset BimolReactionCode) :
    IsSpeciesSwapCanonical S ∨ IsSpeciesSwapCanonical (swapBimolReactionSet S) := by
  rcases le_total (bimolCatalogueKey S)
      (bimolCatalogueKey (swapBimolReactionSet S)) with h | h
  · exact Or.inl h
  · right
    simpa [IsSpeciesSwapCanonical] using h

/-- Completeness of the finite source catalogue.  The disjunction records the
only allowed relabelling: swapping the two named species. -/
theorem bimolecular252Catalogue_complete (Q : SmallPlanarNetwork 5)
    (hQ : IsPlanarBimolecular252 Q) :
    ∃ S ∈ bimolecular252Catalogue,
      S = encodedReactionSet Q ∨ S = swapBimolReactionSet (encodedReactionSet Q) := by
  classical
  let T := encodedReactionSet Q
  have hT : IsFiveReactionSourceCode T := encodedReactionSet_valid Q hQ.1 hQ.2.1
  rcases sourceCode_or_swap_isCanonical T with hcan | hcan
  · refine ⟨T, ?_, Or.inl rfl⟩
    rw [bimolecular252Catalogue, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hT, hcan⟩
  · refine ⟨swapBimolReactionSet T, ?_, Or.inr rfl⟩
    have hvalid := swapBimolReactionSet_valid hT
    rw [bimolecular252Catalogue, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hvalid, hcan⟩

/-- Every original reaction is recovered exactly by decoding its source code. -/
theorem encodedReactionSet_recovers (Q : SmallPlanarNetwork 5)
    (hr : Q.ReactantsAtMost 2) (hp : Q.ProductsAtMost 2) (r : Fin 5) :
    (encodeBimolComplex (Q.reactant r), encodeBimolComplex (Q.product r)) ∈
        encodedReactionSet Q ∧
      (encodeBimolComplex (Q.reactant r)).decode = Q.reactant r ∧
      (encodeBimolComplex (Q.product r)).decode = Q.product r := by
  classical
  refine ⟨?_, decode_encodeBimolComplex _ (hr r), decode_encodeBimolComplex _ (hp r)⟩
  exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩

end SmallCusp
