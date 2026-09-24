import Mathlib

namespace FutileCycle

/-- Disjoint substrate, enzyme and intermediate roles. -/
abbrev Species (S E C : Type*) := S ⊕ (E ⊕ C)

inductive Direction
  | bind | unbind | convert
  deriving DecidableEq, Fintype

abbrev Reaction (C : Type*) := C × Direction

structure ConversionSystem (S E C : Type*) where
  input : C → S
  output : C → S
  enzyme : C → E

variable {S E C : Type*} [DecidableEq S] [DecidableEq E] [DecidableEq C]

def reactant (N : ConversionSystem S E C) (x : Species S E C)
    (r : Reaction C) : ℤ :=
  match r.2 with
  | .bind => if x = .inl (N.input r.1) ∨ x = .inr (.inl (N.enzyme r.1)) then 1 else 0
  | .unbind | .convert => if x = .inr (.inr r.1) then 1 else 0

def product (N : ConversionSystem S E C) (x : Species S E C)
    (r : Reaction C) : ℤ :=
  match r.2 with
  | .bind => if x = .inr (.inr r.1) then 1 else 0
  | .unbind => if x = .inl (N.input r.1) ∨ x = .inr (.inl (N.enzyme r.1)) then 1 else 0
  | .convert => if x = .inl (N.output r.1) ∨ x = .inr (.inl (N.enzyme r.1)) then 1 else 0

def stoich (N : ConversionSystem S E C) (x : Species S E C)
    (r : Reaction C) : ℤ := product N x r - reactant N x r

/-- The owner fixes the reaction column; no independent column permutation. -/
structure Child (N : ConversionSystem S E C) (I : Type*) where
  species : I → Species S E C
  species_injective : Function.Injective species
  reaction : I → Reaction C
  reaction_injective : Function.Injective reaction
  supported : ∀ i, 0 < reactant N (species i) (reaction i)

def Child.matrix {N : ConversionSystem S E C} {I : Type*} (J : Child N I) :
    Matrix I I ℤ := fun i j => stoich N (J.species i) (J.reaction j)

theorem free_owns_binding (N : ConversionSystem S E C) (x : S ⊕ E)
    (c : C) (d : Direction)
    (h : 0 < reactant N (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl) x) (c,d)) :
    d = .bind := by
  cases x <;> cases d <;> simp_all [reactant]

theorem intermediate_owns_outgoing (N : ConversionSystem S E C) (c k : C)
    (d : Direction) (h : 0 < reactant N (.inr (.inr c)) (k,d)) :
    c = k ∧ (d = .unbind ∨ d = .convert) := by
  by_cases hck : c = k <;> cases d <;> simp_all [reactant]

theorem intermediate_outgoing_column (N : ConversionSystem S E C) (c k : C)
    (d : Direction) (h : d = .unbind ∨ d = .convert) :
    stoich N (.inr (.inr c)) (k,d) = -(if c = k then 1 else 0) := by
  rcases h with rfl | rfl <;> simp [stoich, product, reactant]

theorem binding_unbinding_cancel (N : ConversionSystem S E C) (x : Species S E C)
    (c : C) : stoich N x (c,.bind) + stoich N x (c,.unbind) = 0 := by
  simp [stoich, product, reactant]

theorem binding_conversion_substrate (N : ConversionSystem S E C) (s : S) (c : C) :
    stoich N (.inl s) (c,.bind) + stoich N (.inl s) (c,.convert) =
      (if s = N.output c then 1 else 0) - (if s = N.input c then 1 else 0) := by
  simp [stoich, product, reactant, sub_eq_add_neg, add_comm]

theorem binding_conversion_enzyme (N : ConversionSystem S E C) (e : E) (c : C) :
    stoich N (.inr (.inl e)) (c,.bind) +
      stoich N (.inr (.inl e)) (c,.convert) = 0 := by
  simp [stoich, product, reactant]

theorem binding_conversion_intermediate (N : ConversionSystem S E C) (k c : C) :
    stoich N (.inr (.inr k)) (c,.bind) +
      stoich N (.inr (.inr k)) (c,.convert) = 0 := by
  simp [stoich, product, reactant]

/-- false indexes kinase arms; true indexes phosphatase arms.
Phosphatase index i represents D_(i+1). -/
def futile (n : ℕ) : ConversionSystem (Fin (n+1)) Bool (Bool × Fin n) where
  input c := if c.1 then c.2.succ else c.2.castSucc
  output c := if c.1 then c.2.castSucc else c.2.succ
  enzyme c := c.1

end FutileCycle
