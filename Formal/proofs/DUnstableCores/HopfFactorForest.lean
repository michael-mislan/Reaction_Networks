import proofs.DUnstableCores.HopfArticulationTower

/-!
# Exact Hopf propagation on finite articulation forests

The decomposition object below is deliberately small.  Its only internal
nodes are block-diagonal forest unions and one-articulation extensions.  The
matrix, its finite index instance, and every recursive child are packaged
together, so the recursion is definitionally source-faithful and cannot hide
a change of coordinates or a branch inverse.
-/

namespace DUnstableCores

universe u

/-- A finite real square matrix together with its exact finite index type. -/
structure FiniteMatrixPackage where
  ι : Type u
  inst : Fintype ι
  A : Matrix ι ι ℝ

/-- Adjoin one articulation coordinate to a packaged branch matrix. -/
def FiniteMatrixPackage.articulation (p : FiniteMatrixPackage.{u})
    (a : ℝ) (r c : p.ι → ℝ) : FiniteMatrixPackage.{u} := by
  letI : Fintype p.ι := p.inst
  exact
    { ι := Unit ⊕ p.ι
      inst := inferInstance
      A := oneArticulationMatrix a r c p.A }

/-- Disjoint union of two packaged factor-forest components. -/
def FiniteMatrixPackage.block (p q : FiniteMatrixPackage.{u}) :
    FiniteMatrixPackage.{u} := by
  letI : Fintype p.ι := p.inst
  letI : Fintype q.ι := q.inst
  exact
    { ι := p.ι ⊕ q.ι
      inst := inferInstance
      A := Matrix.fromBlocks p.A 0 0 q.A }

/-- The finite forest grammar used by the recursive message theorem. -/
inductive FactorForest : FiniteMatrixPackage.{u} → Type (u + 1)
  | leaf (p : FiniteMatrixPackage.{u}) : FactorForest p
  | articulation {p : FiniteMatrixPackage.{u}}
      (tail : FactorForest p) (a : ℝ) (r c : p.ι → ℝ) :
      FactorForest (p.articulation a r c)
  | block {p q : FiniteMatrixPackage.{u}}
      (left : FactorForest p) (right : FactorForest q) :
      FactorForest (p.block q)

/-- Exact terminal alternatives of forest propagation. -/
inductive HopfForestOutcome (omega : ℝ) : Prop
  | localized (p : FiniteMatrixPackage.{u}) (y : p.ι → ℂ)
      (pair : @HasEigenpair p.ι p.inst p.A
        ((omega : ℂ) * Complex.I) y) : HopfForestOutcome omega
  | message (p : FiniteMatrixPackage.{u})
      (a : ℝ) (r c : p.ι → ℝ)
      (witness : Nonempty
        (@HopfBranchSolveWitness p.ι p.inst a r c p.A omega)) :
      HopfForestOutcome omega

/-- A direct eigenpair of a block-diagonal matrix is carried by at least one
diagonal block.  This retains the eigenvector and uses no characteristic-root
conversion. -/
theorem eigenpair_blockDiagonal_localizes
    {m n : Type u} [Fintype m] [Fintype n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) (lambda : ℂ)
    (z : m ⊕ n → ℂ)
    (hpair : HasEigenpair (Matrix.fromBlocks A 0 0 D) lambda z) :
    (∃ x : m → ℂ, HasEigenpair A lambda x) ∨
      (∃ y : n → ℂ, HasEigenpair D lambda y) := by
  classical
  let x : m → ℂ := fun i => z (Sum.inl i)
  let y : n → ℂ := fun j => z (Sum.inr j)
  have hxEq : ∀ i, Matrix.mulVec (complexify A) x i = lambda * x i := by
    intro i
    have hi := hpair.2 (Sum.inl i)
    simp only [Matrix.mulVec, dotProduct] at hi
    rw [Fintype.sum_sum_type] at hi
    simpa [x, complexify, Matrix.fromBlocks] using hi
  have hyEq : ∀ j, Matrix.mulVec (complexify D) y j = lambda * y j := by
    intro j
    have hj := hpair.2 (Sum.inr j)
    simp only [Matrix.mulVec, dotProduct] at hj
    rw [Fintype.sum_sum_type] at hj
    simpa [y, complexify, Matrix.fromBlocks] using hj
  by_cases hx : x ≠ 0
  · exact Or.inl ⟨x, hx, hxEq⟩
  · right
    have hy : y ≠ 0 := by
      intro hy0
      apply hpair.1
      funext k
      cases k with
      | inl i => exact congrFun (not_ne_iff.mp hx) i
      | inr j => exact congrFun hy0 j
    exact ⟨y, hy, hyEq⟩

/-- Every imaginary eigenpair on the finite factor-forest grammar terminates
either at a leaf component carrying the same pair or at the first exact
inverse-free articulation message.  Block nodes choose a nonzero component;
articulation nodes use the normalized zero/nonzero-coordinate dichotomy. -/
theorem imaginary_eigenpair_factorForest_propagates
    {p : FiniteMatrixPackage.{u}} (forest : FactorForest p)
    (omega : ℝ) (z : p.ι → ℂ)
    (hpair : @HasEigenpair p.ι p.inst p.A
      ((omega : ℂ) * Complex.I) z) :
    HopfForestOutcome.{u} omega := by
  induction forest with
  | leaf p =>
      exact HopfForestOutcome.localized p z hpair
  | @articulation p tail a r c ih =>
      letI : Fintype p.ι := p.inst
      cases imaginary_eigenpair_oneArticulation_dichotomy
          a r c p.A omega z hpair with
      | inl hlocal =>
          obtain ⟨y, hy⟩ := hlocal
          exact ih y hy
      | inr hmessage =>
          exact HopfForestOutcome.message p a r c hmessage
  | @block p q left right ihLeft ihRight =>
      letI : Fintype p.ι := p.inst
      letI : Fintype q.ι := q.inst
      cases eigenpair_blockDiagonal_localizes p.A q.A
          ((omega : ℂ) * Complex.I) z hpair with
      | inl hleft =>
          obtain ⟨x, hx⟩ := hleft
          exact ihLeft x hx
      | inr hright =>
          obtain ⟨y, hy⟩ := hright
          exact ihRight y hy

end DUnstableCores
