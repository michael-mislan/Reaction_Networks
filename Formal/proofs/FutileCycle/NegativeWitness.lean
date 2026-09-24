import proofs.FutileCycle.Source

namespace FutileCycle

def negativeSpecies : Fin 6 → Species (Fin 4) Bool (Bool × Fin 3) :=
  ![.inl 1, .inl 3, .inr (.inl false), .inr (.inl true),
    .inr (.inr (false,2)), .inr (.inr (true,0))]

def negativeReactions : Fin 6 → Reaction (Bool × Fin 3) :=
  ![((false,1),.bind), ((true,2),.bind), ((false,2),.bind),
    ((true,0),.bind), ((false,2),.convert), ((true,0),.convert)]

def negativeChild : Child (futile 3) (Fin 6) where
  species := negativeSpecies
  species_injective := by decide
  reaction := negativeReactions
  reaction_injective := by decide
  supported := by decide

def negativeMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![-1,0,0,-1,0,0; 0,-1,0,0,1,0; -1,0,-1,0,1,0;
    0,-1,0,-1,0,1; 0,0,1,0,-1,0; 0,0,0,1,0,-1]

theorem negativeChild_matrix : negativeChild.matrix = negativeMatrix := by decide

end FutileCycle
