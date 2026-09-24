import Mathlib

/-!
# Literal source semantics for small planar mass-action networks

This file freezes the quantified source classes before enumeration.  A network
is literally a finite list of distinct directed reactions between two-species
complexes.  Molecularity, rank, and dynamical predicates are not hidden in a
graph quotient.
-/

open scoped BigOperators

namespace SmallCusp

abbrev Species := Fin 2
abbrev Complex := Species → ℕ

def molecularity (y : Complex) : ℕ := ∑ i, y i

def swapComplex (y : Complex) : Complex := fun i => y (Fin.rev i)

structure SmallPlanarNetwork (m : ℕ) where
  reactant : Fin m → Complex
  product : Fin m → Complex
  noSelfReaction : ∀ r, reactant r ≠ product r
  reactionInjective : Function.Injective (fun r => (reactant r, product r))

namespace SmallPlanarNetwork

variable {m : ℕ} (Q : SmallPlanarNetwork m)

def stoich (i : Species) (r : Fin m) : ℤ :=
  (Q.product r i : ℤ) - (Q.reactant r i : ℤ)

/-- For a two-row stoichiometric matrix, a nonzero two-by-two minor is exactly
the literal rank-two condition. -/
def HasStoichiometricRankTwo : Prop :=
  ∃ r s : Fin m,
    Q.stoich 0 r * Q.stoich 1 s - Q.stoich 0 s * Q.stoich 1 r ≠ 0

def UsesBothSpecies : Prop :=
  ∀ i : Species, ∃ r : Fin m, Q.stoich i r ≠ 0

def ReactantsAtMost (d : ℕ) : Prop := ∀ r, molecularity (Q.reactant r) ≤ d
def ProductsAtMost (d : ℕ) : Prop := ∀ r, molecularity (Q.product r) ≤ d

def monomial (r : Fin m) (x : Species → ℝ) : ℝ :=
  ∏ i : Species, x i ^ Q.reactant r i

def massAction (k : Fin m → ℝ) (x : Species → ℝ) (i : Species) : ℝ :=
  ∑ r : Fin m, (Q.stoich i r : ℝ) * k r * Q.monomial r x

def multiDerivativeMonomial
    (r : Fin m) (d : Species → ℕ) (x : Species → ℝ) : ℝ :=
  ∏ i : Species,
    ((Q.reactant r i).descFactorial (d i) : ℝ) *
      x i ^ (Q.reactant r i - d i)

def unitMultiIndex (j : Species) : Species → ℕ := fun i => if i = j then 1 else 0

def pairMultiIndex (j l : Species) : Species → ℕ :=
  fun i => (if i = j then 1 else 0) + (if i = l then 1 else 0)

def jacobian (k : Fin m → ℝ) (x : Species → ℝ) (i j : Species) : ℝ :=
  ∑ r : Fin m, (Q.stoich i r : ℝ) * k r *
    Q.multiDerivativeMonomial r (unitMultiIndex j) x

def hessian (k : Fin m → ℝ) (x : Species → ℝ)
    (i j l : Species) : ℝ :=
  ∑ r : Fin m, (Q.stoich i r : ℝ) * k r *
    Q.multiDerivativeMonomial r (pairMultiIndex j l) x

def jacobianApply (k : Fin m → ℝ) (x v : Species → ℝ) (i : Species) : ℝ :=
  ∑ j : Species, Q.jacobian k x i j * v j

def hessianApply (k : Fin m → ℝ) (x u v : Species → ℝ) (i : Species) : ℝ :=
  ∑ j : Species, ∑ l : Species, Q.hessian k x i j l * u j * v l

def rateFieldVariation (u : Fin m → ℝ) (x : Species → ℝ) (i : Species) : ℝ :=
  ∑ r : Fin m, (Q.stoich i r : ℝ) * u r * Q.monomial r x

def rateJacobianVariation (u : Fin m → ℝ) (x q : Species → ℝ)
    (i : Species) : ℝ :=
  ∑ r : Fin m, ∑ j : Species,
    (Q.stoich i r : ℝ) * u r *
      Q.multiDerivativeMonomial r (unitMultiIndex j) x * q j

end SmallPlanarNetwork

def IsPlanarBimolecular252 (Q : SmallPlanarNetwork 5) : Prop :=
  Q.ReactantsAtMost 2 ∧ Q.ProductsAtMost 2 ∧
    Q.HasStoichiometricRankTwo ∧ Q.UsesBothSpecies

def IsPlanarQuadraticTrimolecular252 (Q : SmallPlanarNetwork 5) : Prop :=
  Q.ReactantsAtMost 2 ∧ Q.ProductsAtMost 3 ∧
    Q.HasStoichiometricRankTwo ∧ Q.UsesBothSpecies

def IsPlanarBimolecular242 (Q : SmallPlanarNetwork 4) : Prop :=
  Q.ReactantsAtMost 2 ∧ Q.ProductsAtMost 2 ∧
    Q.HasStoichiometricRankTwo ∧ Q.UsesBothSpecies

def PositiveVector {n : ℕ} (v : Fin n → ℝ) : Prop := ∀ i, 0 < v i
def NonnegativeVector {n : ℕ} (v : Fin n → ℝ) : Prop := ∀ i, 0 ≤ v i

def dot (u v : Species → ℝ) : ℝ := ∑ i : Species, u i * v i

structure CuspCertificate {m : ℕ} (Q : SmallPlanarNetwork m) where
  state : Species → ℝ
  rates : Fin m → ℝ
  rightKernel : Species → ℝ
  leftKernel : Species → ℝ
  centerCorrection : Species → ℝ
  unfoldingDirections : Fin 2 → Fin m → ℝ

namespace CuspCertificate

variable {m : ℕ} {Q : SmallPlanarNetwork m}

def unfoldingEntry (C : CuspCertificate Q) (row col : Fin 2) : ℝ :=
  if row = 0 then
    dot C.leftKernel (Q.rateFieldVariation (C.unfoldingDirections col) C.state)
  else
    dot C.leftKernel
      (Q.rateJacobianVariation (C.unfoldingDirections col) C.state C.rightKernel)

def unfoldingMatrix (C : CuspCertificate Q) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => C.unfoldingEntry i j

def Valid (C : CuspCertificate Q) : Prop :=
  PositiveVector C.state ∧
  PositiveVector C.rates ∧
  (∀ i, Q.massAction C.rates C.state i = 0) ∧
  (∀ i, Q.jacobianApply C.rates C.state C.rightKernel i = 0) ∧
  (∀ j, ∑ i : Species, C.leftKernel i * Q.jacobian C.rates C.state i j = 0) ∧
  dot C.leftKernel C.rightKernel = 1 ∧
  Q.jacobian C.rates C.state 0 0 + Q.jacobian C.rates C.state 1 1 ≠ 0 ∧
  dot C.leftKernel
      (Q.hessianApply C.rates C.state C.rightKernel C.rightKernel) = 0 ∧
  (∀ i, Q.jacobianApply C.rates C.state C.centerCorrection i =
      -Q.hessianApply C.rates C.state C.rightKernel C.rightKernel i) ∧
  dot C.leftKernel C.centerCorrection = 0 ∧
  dot C.leftKernel
      (Q.hessianApply C.rates C.state C.rightKernel C.centerCorrection) ≠ 0 ∧
  Matrix.det C.unfoldingMatrix ≠ 0

end CuspCertificate

def AdmitsTransverseCusp {m : ℕ} (Q : SmallPlanarNetwork m) : Prop :=
  ∃ C : CuspCertificate Q, C.Valid

def IsPlanarAsymptoticallyStableAt {m : ℕ} (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x : Species → ℝ) : Prop :=
  (∀ i, Q.massAction k x i = 0) ∧
  Q.jacobian k x 0 0 + Q.jacobian k x 1 1 < 0 ∧
  Q.jacobian k x 0 0 * Q.jacobian k x 1 1 -
    Q.jacobian k x 0 1 * Q.jacobian k x 1 0 > 0

def AdmitsMultiplePositiveStableEquilibria {m : ℕ}
    (Q : SmallPlanarNetwork m) : Prop :=
  ∃ k x y, PositiveVector k ∧ PositiveVector x ∧ PositiveVector y ∧ x ≠ y ∧
    IsPlanarAsymptoticallyStableAt Q k x ∧ IsPlanarAsymptoticallyStableAt Q k y

def AdmitsMultipleNonnegativeStableEquilibria {m : ℕ}
    (Q : SmallPlanarNetwork m) : Prop :=
  ∃ k x y, PositiveVector k ∧ NonnegativeVector x ∧ NonnegativeVector y ∧ x ≠ y ∧
    IsPlanarAsymptoticallyStableAt Q k x ∧ IsPlanarAsymptoticallyStableAt Q k y

/-- Literal isomorphism permits only a reaction permutation and the optional
swap of the two named species. -/
def LiteralIsomorphic {m : ℕ} (Q P : SmallPlanarNetwork m) : Prop :=
  ∃ e : Equiv.Perm (Fin m),
    ((∀ r, P.reactant (e r) = Q.reactant r ∧ P.product (e r) = Q.product r) ∨
     (∀ r, P.reactant (e r) = swapComplex (Q.reactant r) ∧
       P.product (e r) = swapComplex (Q.product r)))

/-- Simple equivalence keeps reactant labels and permits positive independent
column scalings of the stoichiometric vectors. -/
def SimplyEquivalent {m : ℕ} (Q P : SmallPlanarNetwork m) : Prop :=
  ∃ e : Equiv.Perm (Fin m), ∃ c : Fin m → ℝ, PositiveVector c ∧
    (∀ r, P.reactant (e r) = Q.reactant r) ∧
    (∀ i r, (P.stoich i (e r) : ℝ) = c r * (Q.stoich i r : ℝ))

/-- Diagonal equivalence additionally permits positive row scalings, recorded
separately from literal and simple equivalence. -/
def DiagonallyEquivalent {m : ℕ} (Q P : SmallPlanarNetwork m) : Prop :=
  ∃ e : Equiv.Perm (Fin m), ∃ row : Species → ℝ, ∃ col : Fin m → ℝ,
    PositiveVector row ∧ PositiveVector col ∧
    (∀ r, P.reactant (e r) = Q.reactant r) ∧
    (∀ i r, (P.stoich i (e r) : ℝ) = row i * col r * (Q.stoich i r : ℝ))

/-- Dynamic equivalence is intentionally the strongest, vector-field-family
predicate and is not identified definitionally with any graph quotient. -/
def DynamicallyEquivalent {m n : ℕ}
    (Q : SmallPlanarNetwork m) (P : SmallPlanarNetwork n) : Prop :=
  (∀ k, PositiveVector k → ∃ l, PositiveVector l ∧
    ∀ x i, Q.massAction k x i = P.massAction l x i) ∧
  (∀ l, PositiveVector l → ∃ k, PositiveVector k ∧
    ∀ x i, P.massAction l x i = Q.massAction k x i)

theorem bimolecular252_is_quadraticTrimolecular252
    {Q : SmallPlanarNetwork 5} (h : IsPlanarBimolecular252 Q) :
    IsPlanarQuadraticTrimolecular252 Q := by
  rcases h with ⟨hr, hp, hRank, hUses⟩
  exact ⟨hr, fun r => (hp r).trans (by decide), hRank, hUses⟩

end SmallCusp
