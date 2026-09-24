import proofs.DUnstableCores.HopfMatching
import proofs.DUnstableCores.PositiveRealChild
import proofs.DUnstableCores.StationaryCycleFace

/-!
# Alternating exchange of a literal source matching

An alternating cycle keeps the matched species table fixed and permutes its
reaction table.  When every exchanged pair is a literal reactant incidence,
the result is another source-valid `IndexedMatching`, hence another genuine
whole-column child selection.  This is the combinatorial half of the
certificate-or-exchange route at `DUC-HOPF-SUPPORT`.
-/

namespace AutocatalyticCS.IndexedMatching

open DUnstableCores

variable {X R : Type*} [DecidableEq X] [DecidableEq R]
variable {Q : ReactionNetwork X R}

/-- Permute the reaction endpoints of a matching while retaining its species
endpoints.  The only new obligation is literal reactant eligibility. -/
def permuteRight (E : IndexedMatching Q) (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i))) :
    IndexedMatching Q where
  card := E.card
  left := E.left
  right := fun i => E.right (sigma i)
  left_injective := E.left_injective
  right_injective := E.right_injective.comp sigma.injective
  reactant_edge := hreact

omit [DecidableEq X] [DecidableEq R] in
@[simp] theorem permuteRight_left
    (E : IndexedMatching Q) (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i))) (i) :
    (E.permuteRight sigma hreact).left i = E.left i := rfl

omit [DecidableEq X] [DecidableEq R] in
@[simp] theorem permuteRight_right
    (E : IndexedMatching Q) (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i))) (i) :
    (E.permuteRight sigma hreact).right i = E.right (sigma i) := rfl

omit [DecidableEq R] in
theorem permuteRight_species
    (E : IndexedMatching Q) (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i))) :
    (E.permuteRight sigma hreact).species = E.species := rfl

omit [DecidableEq X] in
theorem permuteRight_reactions
    (E : IndexedMatching Q) (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i))) :
    (E.permuteRight sigma hreact).reactions = E.reactions := by
  ext r
  simp only [reactions, Finset.mem_image, Finset.mem_univ, true_and,
    permuteRight_right]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨sigma i, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨sigma.symm j, by simp⟩

/-- The exchanged matching yields a genuine child on exactly the original
species and reaction sets. -/
theorem permuteRight_child_sets
    (E : IndexedMatching Q) (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i))) :
    (E.permuteRight sigma hreact).toChildSelection.species = E.species ∧
      (E.permuteRight sigma hreact).toChildSelection.reactions = E.reactions := by
  exact ⟨E.permuteRight_species sigma hreact,
    E.permuteRight_reactions sigma hreact⟩

/-- Every assigned edge of the exchanged child is exactly an original species
endpoint paired with the reaction at a permuted matching index. -/
theorem permuteRight_child_exists_index
    (E : IndexedMatching Q) (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i)))
    (x : (E.permuteRight sigma hreact).toChildSelection.species) :
    ∃ i : Fin E.card,
      E.left i = x.1 ∧
        E.right (sigma i) =
          ((E.permuteRight sigma hreact).toChildSelection.assign x).1 := by
  simpa using (E.permuteRight sigma hreact).exists_index_of_species x

/-- The canonical enumeration of the species endpoint set by matching index. -/
noncomputable def indexSpeciesEquiv (E : IndexedMatching Q) :
    Fin E.card ≃ E.species :=
  Equiv.ofBijective
    (fun i => ⟨E.left i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨by
      intro i j hij
      exact E.left_injective (congrArg Subtype.val hij), by
      intro x
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
      exact ⟨i, Subtype.ext hi⟩⟩

theorem toChildSelection_assign_indexSpeciesEquiv
    (E : IndexedMatching Q) (i : Fin E.card) :
    (E.toChildSelection.assign (E.indexSpeciesEquiv i)).1 = E.right i := by
  obtain ⟨k, hleft, hright⟩ :=
    E.exists_index_of_species (E.indexSpeciesEquiv i)
  change E.left k = E.left i at hleft
  have hki : k = i := E.left_injective hleft
  subst k
  exact hright.symm

theorem permuteRight_assign_indexSpeciesEquiv
    (E : IndexedMatching Q) (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i)))
    (i : Fin E.card) :
    ((E.permuteRight sigma hreact).toChildSelection.assign
      (E.indexSpeciesEquiv i)).1 = E.right (sigma i) := by
  obtain ⟨k, hleft, hright⟩ :=
    (E.permuteRight sigma hreact).exists_index_of_species
      (E.indexSpeciesEquiv i)
  change E.left k = E.left i at hleft
  have hki : k = i := E.left_injective hleft
  subst k
  exact hright.symm

end AutocatalyticCS.IndexedMatching

namespace DUnstableCores

/-- A strictly negative literal stoichiometric coefficient can only arise
from a positive reactant multiplicity.  Unlike the converse, this inference
is source-faithful even in the presence of catalysts. -/
theorem reactant_of_stoich_neg
    {Species Reaction : Type*} {Q : SourceNetwork Species Reaction}
    {s : Species} {r : Reaction}
    (hneg : Q.stoich s r < 0) : Q.Reactant s r := by
  change (Q.product s r : ℤ) - (Q.reactant s r : ℤ) < 0 at hneg
  change 0 < Q.reactant s r
  omega

variable {Species Reaction : Type*} [DecidableEq Species]
  [DecidableEq Reaction]

/-- Regard a permuted matching on the forgotten reaction network as the
corresponding child of its full literal source.  The type annotation records
the source needed by the real-matrix semantics. -/
def permuteRightSourceChild
    {Q : SourceNetwork Species Reaction}
    (E : AutocatalyticCS.IndexedMatching Q.toReactionNetwork)
    (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i))) :
    ChildSelection Q :=
  (E.permuteRight sigma hreact).toChildSelection

/-- A negative determinant on an admissible exchanged source matching is
already the strict spectral branch of the certificate-or-exchange dichotomy.
`permuteRight` supplies literal source validity and positive-real localization
supplies D-instability. -/
theorem permuteRight_sourceChild_dUnstable_of_det_neg
    {Q : SourceNetwork Species Reaction}
    (E : AutocatalyticCS.IndexedMatching Q.toReactionNetwork)
    (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i)))
    (hdet : Matrix.det
      (-(permuteRightSourceChild E sigma hreact).realMatrix) < 0) :
    DUnstable (permuteRightSourceChild E sigma hreact).realMatrix := by
  exact det_neg_negative_implies_dUnstable
    (permuteRightSourceChild E sigma hreact).realMatrix hdet

/-- An admissible exchanged matching whose child matrix is an odd column
permutation of the anchor has the opposite signed determinant.  The explicit
assignment equation is the small typed interface needed to identify the
abstract permutation with a concrete alternating face exchange. -/
theorem permuteRight_sourceChild_dUnstable_of_odd_exchange
    {Q : SourceNetwork Species Reaction}
    (E : AutocatalyticCS.IndexedMatching Q.toReactionNetwork)
    (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i)))
    (tau : Equiv.Perm E.species)
    (hodd : Equiv.Perm.sign tau = -1)
    (hassign : ∀ x : E.species,
      ((permuteRightSourceChild E sigma hreact).assign x).1 =
        (E.toChildSelection.assign (tau x)).1)
    (hanchor : 0 < Matrix.det
      (-(ChildSelection.realMatrix (Q := Q) E.toChildSelection))) :
    DUnstable (permuteRightSourceChild E sigma hreact).realMatrix := by
  have hmatrix :
      -(permuteRightSourceChild E sigma hreact).realMatrix =
        (-(ChildSelection.realMatrix (Q := Q) E.toChildSelection)).submatrix id tau := by
    ext i j
    change -(Q.stoich i.1
        ((permuteRightSourceChild E sigma hreact).assign j).1 : ℝ) =
      -(Q.stoich i.1 (E.toChildSelection.assign (tau j)).1 : ℝ)
    rw [hassign]
  apply permuteRight_sourceChild_dUnstable_of_det_neg E sigma hreact
  rw [hmatrix]
  have hdet := Matrix.det_permute' tau
    (-(ChildSelection.realMatrix (Q := Q) E.toChildSelection))
  rw [hodd] at hdet
  norm_num at hdet
  calc
    Matrix.det ((-(ChildSelection.realMatrix (Q := Q) E.toChildSelection)).submatrix
        id tau) = -Matrix.det
          (-(ChildSelection.realMatrix (Q := Q) E.toChildSelection)) := hdet
    _ < 0 := neg_neg_of_pos hanchor

/-- The assignment equation and species parity in the preceding theorem are
canonical: conjugating the reaction-index permutation by the matching's
species enumeration produces them automatically. -/
theorem permuteRight_sourceChild_dUnstable_of_odd_index_exchange
    {Q : SourceNetwork Species Reaction}
    (E : AutocatalyticCS.IndexedMatching Q.toReactionNetwork)
    (sigma : Equiv.Perm (Fin E.card))
    (hreact : ∀ i, 0 < Q.reactant (E.left i) (E.right (sigma i)))
    (hodd : Equiv.Perm.sign sigma = -1)
    (hanchor : 0 < Matrix.det
      (-(ChildSelection.realMatrix (Q := Q) E.toChildSelection))) :
    DUnstable (permuteRightSourceChild E sigma hreact).realMatrix := by
  let e := E.indexSpeciesEquiv
  let tau : Equiv.Perm E.species := (e.symm.trans sigma).trans e
  apply permuteRight_sourceChild_dUnstable_of_odd_exchange
    E sigma hreact tau
  · have heq : Equiv.Perm.sign tau = Equiv.Perm.sign sigma := by
      exact Equiv.Perm.sign_symm_trans_trans sigma e
    exact heq.trans hodd
  · intro x
    let i := e.symm x
    have hx : e i = x := e.apply_symm_apply x
    rw [← hx]
    have htau : tau (e i) = e (sigma i) := by simp [tau]
    rw [htau]
    exact (E.permuteRight_assign_indexSpeciesEquiv sigma hreact i).trans
      (E.toChildSelection_assign_indexSpeciesEquiv (sigma i)).symm
  · exact hanchor

/-- Concrete two-index source adapter.  Two negative crossed stoichiometric
entries make the transposition reactant-admissible; its odd parity then turns
any positive-determinant anchor into a genuine D-unstable source child. -/
theorem swapRight_sourceChild_dUnstable_of_crossed_stoich_neg
    {Q : SourceNetwork Species Reaction}
    (E : AutocatalyticCS.IndexedMatching Q.toReactionNetwork)
    (i j : Fin E.card) (hij : i ≠ j)
    (hijneg : (Q.stoich (E.left i) (E.right j) : ℝ) < 0)
    (hjineg : (Q.stoich (E.left j) (E.right i) : ℝ) < 0)
    (hanchor : 0 < Matrix.det
      (-(ChildSelection.realMatrix (Q := Q) E.toChildSelection))) :
    DUnstable (permuteRightSourceChild E (Equiv.swap i j) (by
      intro k
      by_cases hki : k = i
      · subst k
        rw [Equiv.swap_apply_left]
        apply reactant_of_stoich_neg
        exact_mod_cast hijneg
      by_cases hkj : k = j
      · subst k
        rw [Equiv.swap_apply_right]
        apply reactant_of_stoich_neg
        exact_mod_cast hjineg
      rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      exact E.reactant_edge k)).realMatrix := by
  apply permuteRight_sourceChild_dUnstable_of_odd_index_exchange
  · exact Equiv.Perm.sign_swap hij
  · exact hanchor

/-- The same crossed-stoichiometry transposition, promoted through finite
principal descent to the literature-facing minimal-core conclusion. -/
theorem crossed_stoich_swap_yields_DUnstableCore
    {Q : SourceNetwork Species Reaction}
    (E : AutocatalyticCS.IndexedMatching Q.toReactionNetwork)
    (i j : Fin E.card) (hij : i ≠ j)
    (hijneg : (Q.stoich (E.left i) (E.right j) : ℝ) < 0)
    (hjineg : (Q.stoich (E.left j) (E.right i) : ℝ) < 0)
    (hanchor : 0 < Matrix.det
      (-(ChildSelection.realMatrix (Q := Q) E.toChildSelection))) :
    ∃ core : ChildSelection Q, IsDUnstableCore core := by
  let hreact : ∀ k,
      0 < Q.reactant (E.left k) (E.right ((Equiv.swap i j) k)) := by
    intro k
    by_cases hki : k = i
    · subst k
      rw [Equiv.swap_apply_left]
      apply reactant_of_stoich_neg
      exact_mod_cast hijneg
    by_cases hkj : k = j
    · subst k
      rw [Equiv.swap_apply_right]
      apply reactant_of_stoich_neg
      exact_mod_cast hjineg
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    exact E.reactant_edge k
  have hchild : DUnstable
      (permuteRightSourceChild E (Equiv.swap i j) hreact).realMatrix := by
    apply permuteRight_sourceChild_dUnstable_of_odd_index_exchange
    · exact Equiv.Perm.sign_swap hij
    · exact hanchor
  obtain ⟨core, -, hcore⟩ := dUnstable_childSelection_contains_core
    (permuteRightSourceChild E (Equiv.swap i j) hreact) hchild
  exact ⟨core, hcore⟩

/-- Two same-sign candidate exchange pairs and one alternating negative
cross-product force one candidate pair to be negative.  The canonical swap
adapter then turns that sign alternative directly into a minimal source core. -/
theorem alternating_crossed_pairs_yield_DUnstableCore
    {Q : SourceNetwork Species Reaction}
    (E : AutocatalyticCS.IndexedMatching Q.toReactionNetwork)
    (i₀ j₀ i₁ j₁ : Fin E.card) (hne₀ : i₀ ≠ j₀) (hne₁ : i₁ ≠ j₁)
    (hpair₀ : 0 <
      (Q.stoich (E.left i₀) (E.right j₀) : ℝ) *
        (Q.stoich (E.left j₀) (E.right i₀) : ℝ))
    (hpair₁ : 0 <
      (Q.stoich (E.left i₁) (E.right j₁) : ℝ) *
        (Q.stoich (E.left j₁) (E.right i₁) : ℝ))
    (hcross :
      (Q.stoich (E.left i₁) (E.right j₁) : ℝ) *
        (Q.stoich (E.left j₀) (E.right i₀) : ℝ) < 0)
    (hanchor : 0 < Matrix.det
      (-(ChildSelection.realMatrix (Q := Q) E.toChildSelection))) :
    ∃ core : ChildSelection Q, IsDUnstableCore core := by
  have hsign := alternatingCoupling_negative_pair
    (Q.stoich (E.left i₀) (E.right j₀) : ℝ)
    (Q.stoich (E.left i₁) (E.right j₁) : ℝ)
    (Q.stoich (E.left j₀) (E.right i₀) : ℝ)
    (Q.stoich (E.left j₁) (E.right i₁) : ℝ)
    hpair₀ hpair₁ hcross
  rcases hsign with hneg₀ | hneg₁
  · exact crossed_stoich_swap_yields_DUnstableCore
      E i₀ j₀ hne₀ hneg₀.1 hneg₀.2 hanchor
  · exact crossed_stoich_swap_yields_DUnstableCore
      E i₁ j₁ hne₁ hneg₁.1 hneg₁.2 hanchor

end DUnstableCores
