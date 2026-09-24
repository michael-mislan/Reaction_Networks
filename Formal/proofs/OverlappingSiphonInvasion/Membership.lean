import proofs.CoreCriticalSiphon.Face

namespace OverlappingSiphonInvasion
open CoreCriticalSiphon

/-- An actual coordinate derivative of the literal mass-action field. -/
noncomputable def normalEntry (Q : SourceCRN) (k : Q.Reaction → ℝ)
    (y : Q.Species → ℝ) (i j : Q.Species) : ℝ :=
  deriv (fun t : ℝ => Q.massAction k (fun l => y l + if l = j then t else 0) i) 0

theorem massAction_zero_on_siphon (Q : SourceCRN) (k : Q.Reaction → ℝ)
    (hk : ∀ r, 0 < k r) (S : Finset Q.Species) (hS : IsSiphon Q S)
    (y : Q.Species → ℝ) (hy : y ∈ BoundaryFace Q S) (i : Q.Species) (hi : i ∈ S) :
    Q.massAction k y i = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  exact siphon_implies_universallyFaceInvariant Q hS r (k r) (hk r) y hy i hi

/-- Differentiating an invariant coordinate face forces the structural zero. -/
theorem normalEntry_zero (Q : SourceCRN) (k : Q.Reaction → ℝ)
    (hk : ∀ r, 0 < k r) (S : Finset Q.Species) (hS : IsSiphon Q S)
    (y : Q.Species → ℝ) (hy : y ∈ BoundaryFace Q S)
    (i j : Q.Species) (hi : i ∈ S) (hj : j ∉ S) : normalEntry Q k y i j = 0 := by
  have hz : (fun t : ℝ => Q.massAction k (fun l => y l + if l = j then t else 0) i) =
      fun _ => 0 := by
    funext t
    apply massAction_zero_on_siphon Q k hk S hS _ _ i hi
    intro l hl
    have hlj : l ≠ j := fun h => hj (h ▸ hl)
    simp [hlj, hy l hl]
  simp [normalEntry, hz]

/-- Nonzero first-order production can only decrease siphon membership. -/
theorem normalEntry_membership (Q : SourceCRN) (k : Q.Reaction → ℝ)
    (hk : ∀ r, 0 < k r) {A : Type*} (S : A → Finset Q.Species)
    (hS : ∀ a, IsSiphon Q (S a)) (y : Q.Species → ℝ)
    (hy : ∀ a, y ∈ BoundaryFace Q (S a)) (i j : Q.Species)
    (hij : normalEntry Q k y i j ≠ 0) : ∀ a, i ∈ S a → j ∈ S a := by
  intro a hi
  by_contra hj
  exact hij (normalEntry_zero Q k hk (S a) (hS a) y (hy a) i j hi hj)

/-- Cardinality ordering of signatures already supplies a finite triangular
factorization; distinct signatures of equal size cannot exchange entries. -/
theorem membership_blockTriangular {n a R : Type*} [Fintype a] [DecidableEq a]
    [Zero R] (M : Matrix n n R) (S : n → Finset a)
    (h : ∀ i j, M i j ≠ 0 → S i ⊆ S j) : M.BlockTriangular (fun i => (S i).card) := by
  intro i j hij
  by_contra hne
  exact (not_le_of_gt hij) (Finset.card_le_card (h i j hne))

theorem membership_card_charpoly {n a R : Type*} [Fintype n] [DecidableEq n]
    [Fintype a] [DecidableEq a] [CommRing R]
    (M : Matrix n n R) (S : n → Finset a)
    (h : ∀ i j, M i j ≠ 0 → S i ⊆ S j) :
    M.charpoly = ∏ c ∈ Finset.univ.image (fun i => (S i).card),
      (M.toSquareBlock (fun i => (S i).card) c).charpoly :=
  (membership_blockTriangular M S h).charpoly

end OverlappingSiphonInvasion
