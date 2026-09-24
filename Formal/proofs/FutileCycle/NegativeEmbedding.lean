import proofs.FutileCycle.NegativeWitness

namespace FutileCycle

def negativeSpeciesAt (n : ℕ) (hn : 3 ≤ n) : Fin 6 → Species (Fin (n+1)) Bool (Bool × Fin n) :=
  ![.inl ⟨1, by omega⟩, .inl ⟨3, by omega⟩, .inr (.inl false), .inr (.inl true),
    .inr (.inr (false,⟨2, by omega⟩)), .inr (.inr (true,⟨0, by omega⟩))]

def negativeReactionsAt (n : ℕ) (hn : 3 ≤ n) : Fin 6 → Reaction (Bool × Fin n) :=
  ![((false,⟨1, by omega⟩),.bind), ((true,⟨2, by omega⟩),.bind),
    ((false,⟨2, by omega⟩),.bind), ((true,⟨0, by omega⟩),.bind),
    ((false,⟨2, by omega⟩),.convert), ((true,⟨0, by omega⟩),.convert)]

def negativeChildAt (n : ℕ) (hn : 3 ≤ n) : Child (futile n) (Fin 6) where
  species := negativeSpeciesAt n hn
  species_injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [negativeSpeciesAt]
  reaction := negativeReactionsAt n hn
  reaction_injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [negativeReactionsAt]
  supported := by
    intro i
    fin_cases i <;> norm_num [negativeSpeciesAt, negativeReactionsAt, reactant, futile]

theorem negativeChildAt_matrix (n : ℕ) (hn : 3 ≤ n) :
    (negativeChildAt n hn).matrix = negativeMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Child.matrix, negativeChildAt, negativeSpeciesAt, negativeReactionsAt,
      negativeMatrix, stoich, reactant, product, futile] <;> simp

end FutileCycle
