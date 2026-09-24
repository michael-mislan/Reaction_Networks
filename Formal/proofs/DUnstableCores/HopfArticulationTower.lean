import proofs.DUnstableCores.HopfArticulationDichotomy

/-!
# Finite propagation of inverse-free Hopf messages

This file packages the one-articulation dichotomy into a well-founded finite
tower.  A zero articulation coordinate strictly descends one level.  The
first nonzero articulation coordinate emits the exact inverse-free branch
message.  Thus the iteration terminates without ever assuming that a branch
resolvent is nonsingular.
-/

namespace DUnstableCores

universe u

/-- `HasEigenpair` is independent of the proof-irrelevant choice of finite
enumeration carried by a `Fintype` instance. -/
private theorem hasEigenpair_changeFintype
    {ι : Type u} (inst₁ inst₂ : Fintype ι)
    {A : Matrix ι ι ℝ} {lambda : ℂ} {z : ι → ℂ}
    (h : @HasEigenpair ι inst₁ A lambda z) :
    @HasEigenpair ι inst₂ A lambda z := by
  have hi : inst₁ = inst₂ := Subsingleton.elim _ _
  subst inst₂
  exact h

/-- A matrix obtained by successively adjoining distinguished articulation
coordinates.  The natural-number index is the exact number of available
strict descents. -/
inductive ArticulationTower :
    (n : ℕ) → {ι : Type u} → Matrix ι ι ℝ → Prop
  | leaf {ι : Type u} [Fintype ι] (A : Matrix ι ι ℝ) :
      ArticulationTower 0 A
  | node {n : ℕ} {ι : Type u} [Fintype ι] {B : Matrix ι ι ℝ}
      (tail : ArticulationTower n B) (a : ℝ) (r c : ι → ℝ) :
      ArticulationTower (n + 1) (oneArticulationMatrix a r c B)

/-- The exact trace of finite Hopf propagation.  `descend` records every
zero-coordinate localization; `message` records the first nonzero-coordinate
Schur message; and `leaf` records exhaustion of the supplied tower. -/
inductive HopfPropagationOutcome (omega : ℝ) : ℕ → Prop
  | leaf {ι : Type u} [Fintype ι]
      (B : Matrix ι ι ℝ) (y : ι → ℂ)
      (pair : HasEigenpair B ((omega : ℂ) * Complex.I) y) :
      HopfPropagationOutcome omega 0
  | message {n : ℕ} {ι : Type u} [Fintype ι]
      (a : ℝ) (r c : ι → ℝ) (B : Matrix ι ι ℝ)
      (witness : Nonempty (HopfBranchSolveWitness a r c B omega)) :
      HopfPropagationOutcome omega (n + 1)
  | descend {n : ℕ} (tail : HopfPropagationOutcome omega n) :
      HopfPropagationOutcome omega (n + 1)

/-- Iterating the normalized one-articulation theorem over a finite tower
always terminates in a localized leaf eigenpair or an exact inverse-free Hopf
message.  No inverse, determinant, or branch-resolvent hypothesis occurs. -/
theorem imaginary_eigenpair_articulationTower_propagates
    {n : ℕ} {ι : Type u} [instA : Fintype ι] {A : Matrix ι ι ℝ}
    (tower : ArticulationTower n A) (omega : ℝ) (z : ι → ℂ)
    (hpair : @HasEigenpair ι instA A ((omega : ℂ) * Complex.I) z) :
    HopfPropagationOutcome.{u} omega n := by
  induction n generalizing ι A with
  | zero =>
      cases tower with
      | @leaf ι inst A =>
          have hp : @HasEigenpair ι inst A
              ((omega : ℂ) * Complex.I) z :=
            hasEigenpair_changeFintype instA inst hpair
          exact @HopfPropagationOutcome.leaf.{u} omega ι inst A z hp
  | succ n ih =>
      cases tower with
      | @node _ ι inst B tail a r c =>
          have hp : @HasEigenpair (Unit ⊕ ι) (instFintypeSum Unit ι)
              (oneArticulationMatrix a r c B)
              ((omega : ℂ) * Complex.I) z :=
            hasEigenpair_changeFintype instA _ hpair
          cases imaginary_eigenpair_oneArticulation_dichotomy
              a r c B omega z hp with
          | inl hlocal =>
              obtain ⟨y, hy⟩ := hlocal
              exact HopfPropagationOutcome.descend
                (ih tail y
                  (hasEigenpair_changeFintype inst _ hy))
          | inr hmessage =>
              exact @HopfPropagationOutcome.message.{u} omega n ι inst
                a r c B hmessage

/-- The first nontrivial two-level instance, exposed separately as a compact
interface for downstream tree/forest decomposition. -/
theorem imaginary_eigenpair_twoArticulations_propagates
    {κ : Type u} [Fintype κ]
    (a b : ℝ) (r c : (Unit ⊕ κ) → ℝ) (s t : κ → ℝ)
    (C : Matrix κ κ ℝ) (omega : ℝ)
    (z : Unit ⊕ (Unit ⊕ κ) → ℂ)
    (hpair : HasEigenpair
      (oneArticulationMatrix a r c (oneArticulationMatrix b s t C))
      ((omega : ℂ) * Complex.I) z) :
    (∃ y : κ → ℂ, HasEigenpair C ((omega : ℂ) * Complex.I) y) ∨
      Nonempty (HopfBranchSolveWitness b s t C omega) ∨
      Nonempty (HopfBranchSolveWitness a r c
        (oneArticulationMatrix b s t C) omega) := by
  cases imaginary_eigenpair_oneArticulation_dichotomy
      a r c (oneArticulationMatrix b s t C) omega z hpair with
  | inr houter => exact Or.inr (Or.inr houter)
  | inl hinner =>
      obtain ⟨y, hy⟩ := hinner
      cases imaginary_eigenpair_oneArticulation_dichotomy
          b s t C omega y hy with
      | inl hleaf => exact Or.inl hleaf
      | inr hmessage => exact Or.inr (Or.inl hmessage)

end DUnstableCores
