import proofs.DUnstableCores.Minimality

namespace OscillatoryCores

open DUnstableCores

variable {S R : Type*} [DecidableEq S] [DecidableEq R]

def transportChild {Q Q' : SourceNetwork S R}
    (hR : ∀ i j, Q.Reactant i j → Q'.Reactant i j) (κ : ChildSelection Q) :
    ChildSelection Q' where
  species := κ.species
  reactions := κ.reactions
  assign := κ.assign
  reactant_match := fun i => hR i.1 (κ.assign i).1 (κ.reactant_match i)

omit [DecidableEq S] [DecidableEq R] in
theorem transportChild_matrix {Q Q' : SourceNetwork S R}
    (hR : ∀ i j, Q.Reactant i j → Q'.Reactant i j) (hS : Q.stoich=Q'.stoich)
    (κ : ChildSelection Q) : κ.realMatrix=(transportChild hR κ).realMatrix := by
  change (fun i j : κ.species => (Q.stoich i.1 (κ.assign j).1 : ℝ)) =
    (fun i j : κ.species => (Q'.stoich i.1 (κ.assign j).1 : ℝ))
  exact congrArg (fun M : Matrix S R ℤ => fun i j : κ.species => (M i.1 (κ.assign j).1 : ℝ)) hS

omit [DecidableEq S] [DecidableEq R] in
theorem transport_child_safety {Q Q' : SourceNetwork S R}
    (hR : ∀ i j, Q.Reactant i j → Q'.Reactant i j) (hS : Q.stoich=Q'.stoich)
    (hsafe : ∀ κ : ChildSelection Q', DNonUnstable κ.realMatrix) :
    ∀ κ : ChildSelection Q, DNonUnstable κ.realMatrix := by
  intro κ
  exact (transportChild_matrix hR hS κ).symm ▸ hsafe (transportChild hR κ)

end OscillatoryCores
