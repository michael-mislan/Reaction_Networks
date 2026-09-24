import proofs.OverlappingSiphonInvasion.Membership
import proofs.OverlappingSiphonInvasion.OverlapFactorization

noncomputable section
namespace OverlappingSiphonInvasion
open Matrix CoreCriticalSiphon

variable {U V I : Type*} [Fintype U] [Fintype V] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]

def privateU (u : U) : (U ⊕ V) ⊕ I := Sum.inl (Sum.inl u)
def privateV (v : V) : (U ⊕ V) ⊕ I := Sum.inl (Sum.inr v)
def sharedI (i : I) : (U ⊕ V) ⊕ I := Sum.inr i
def siphonU : U ⊕ I → (U ⊕ V) ⊕ I := Sum.elim privateU sharedI
def siphonV : V ⊕ I → (U ⊕ V) ⊕ I := Sum.elim privateV sharedI

theorem structural_overlap_charpoly (M : Matrix ((U ⊕ V) ⊕ I) ((U ⊕ V) ⊕ I) ℝ)
    (huv : ∀ u v, M (privateU u) (privateV v) = 0)
    (hvu : ∀ v u, M (privateV v) (privateU u) = 0)
    (hiu : ∀ i u, M (sharedI i) (privateU u) = 0)
    (hiv : ∀ i v, M (sharedI i) (privateV v) = 0) :
    M.charpoly * (M.submatrix sharedI sharedI).charpoly =
      (M.submatrix siphonU siphonU).charpoly * (M.submatrix siphonV siphonV).charpoly := by
  let P := M.submatrix privateU privateU
  let Q := M.submatrix privateV privateV
  let C := M.submatrix sharedI sharedI
  let B := M.submatrix privateU sharedI
  let D := M.submatrix privateV sharedI
  have hM : M = fromBlocks (fromBlocks P 0 0 Q)
      (fun x j => Sum.elim (fun x => B x j) (fun x => D x j) x) 0 C := by
    ext x y
    rcases x with (u | v) | i <;> rcases y with (u' | v') | i' <;>
      simp [P,Q,C,B,D,fromBlocks,Matrix.submatrix,privateU,privateV,sharedI] at *
    all_goals first | exact huv _ _ | exact hvu _ _ | exact hiu _ _ | exact hiv _ _
  have hU : M.submatrix siphonU siphonU = fromBlocks P B 0 C := by
    ext x y
    rcases x with u | i <;> rcases y with u' | i' <;>
      simp [P,B,C,fromBlocks,Matrix.submatrix,siphonU,privateU,sharedI] at *
    exact hiu _ _
  have hV : M.submatrix siphonV siphonV = fromBlocks Q D 0 C := by
    ext x y
    rcases x with v | i <;> rcases y with v' | i' <;>
      simp [Q,D,C,fromBlocks,Matrix.submatrix,siphonV,privateV,sharedI] at *
    exact hiv _ _
  rw [hU,hV]
  change M.charpoly*C.charpoly = _
  rw [hM]
  exact overlap_charpoly P Q C B D

/-- The overlap identity for an actual source derivative on any specified
private/private/shared normal coordinate cover. Face invariance supplies every
structural zero; the inputs contain no characteristic-polynomial premise. -/
theorem source_overlap_charpoly (Q : SourceCRN) (k : Q.Reaction → ℝ)
    (hk : ∀ r, 0 < k r) (S₁ S₂ : Finset Q.Species)
    (hS₁ : IsSiphon Q S₁) (hS₂ : IsSiphon Q S₂)
    (y : Q.Species → ℝ) (hy₁ : y ∈ BoundaryFace Q S₁) (hy₂ : y ∈ BoundaryFace Q S₂)
    (e : ((U ⊕ V) ⊕ I) → Q.Species)
    (hu₁ : ∀ u, e (privateU u) ∈ S₁) (hu₂ : ∀ u, e (privateU u) ∉ S₂)
    (hv₁ : ∀ v, e (privateV v) ∉ S₁) (hv₂ : ∀ v, e (privateV v) ∈ S₂)
    (hi₁ : ∀ i, e (sharedI i) ∈ S₁) (hi₂ : ∀ i, e (sharedI i) ∈ S₂) :
    let M : Matrix ((U ⊕ V) ⊕ I) ((U ⊕ V) ⊕ I) ℝ :=
      fun i j => normalEntry Q k y (e i) (e j)
    M.charpoly * (M.submatrix sharedI sharedI).charpoly =
      (M.submatrix siphonU siphonU).charpoly * (M.submatrix siphonV siphonV).charpoly := by
  apply structural_overlap_charpoly
  · intro u v
    exact normalEntry_zero Q k hk S₁ hS₁ y hy₁ _ _ (hu₁ u) (hv₁ v)
  · intro v u
    exact normalEntry_zero Q k hk S₂ hS₂ y hy₂ _ _ (hv₂ v) (hu₂ u)
  · intro i u
    exact normalEntry_zero Q k hk S₂ hS₂ y hy₂ _ _ (hi₂ i) (hu₂ u)
  · intro i v
    exact normalEntry_zero Q k hk S₁ hS₁ y hy₁ _ _ (hi₁ i) (hv₁ v)

end OverlappingSiphonInvasion
