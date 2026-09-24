import proofs.AllIrrRAFCert.Hardness.GuardCycles

namespace AllIrrRAFCert.Hardness

variable {k n : Nat}

def rxnEquiv : Rxn k n ≃ (Vertex k n ⊕ Vertex k n ⊕ Pair k n ⊕ Pair k n ⊕ Unit) where
  toFun
    | .selector v => .inl v
    | .colorGate v => .inr (.inl v)
    | .pairLeft e => .inr (.inr (.inl e))
    | .pairRight e => .inr (.inr (.inr (.inl e)))
    | .close => .inr (.inr (.inr (.inr ())))
  invFun
    | .inl v => .selector v
    | .inr (.inl v) => .colorGate v
    | .inr (.inr (.inl e)) => .pairLeft e
    | .inr (.inr (.inr (.inl e))) => .pairRight e
    | .inr (.inr (.inr (.inr _))) => .close
  left_inv := by intro r; cases r <;> rfl
  right_inv := by rintro (v | v | e | e | u) <;> rfl

def molEquiv : Mol k n ≃ (Unit ⊕ Vertex k n ⊕ Vertex k n ⊕ Fin k ⊕ Pair k n ⊕ Unit) where
  toFun
    | .food => .inl ()
    | .signal v => .inr (.inl v)
    | .guardCat v => .inr (.inr (.inl v))
    | .colorOK i => .inr (.inr (.inr (.inl i)))
    | .pairOK e => .inr (.inr (.inr (.inr (.inl e))))
    | .globalCat => .inr (.inr (.inr (.inr (.inr ()))))
  invFun
    | .inl _ => .food
    | .inr (.inl v) => .signal v
    | .inr (.inr (.inl v)) => .guardCat v
    | .inr (.inr (.inr (.inl i))) => .colorOK i
    | .inr (.inr (.inr (.inr (.inl e)))) => .pairOK e
    | .inr (.inr (.inr (.inr (.inr _)))) => .globalCat
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro (u | v | v | i | e | u) <;> rfl

theorem reaction_count : Fintype.card (Rxn k n) = 2*(k*(n+2)) + 2*(k*(n+2))^2 + 1 := by
  rw [Fintype.card_congr rxnEquiv]
  simp only [Fintype.card_sum,Fintype.card_unit,Vertex,Pair,Fintype.card_prod,Fintype.card_fin]
  ring

theorem molecule_count : Fintype.card (Mol k n) = 2 + 2*(k*(n+2)) + k + (k*(n+2))^2 := by
  rw [Fintype.card_congr molEquiv]
  simp only [Fintype.card_sum,Fintype.card_unit,Vertex,Pair,Fintype.card_prod,Fintype.card_fin]
  ring

def listedFamily (k n : Nat) : Finset (Finset (Rxn k n)) :=
  Finset.univ.image guard

theorem parameter_eq : (listedFamily k n).card = k := by
  rw [listedFamily,Finset.card_image_of_injective _ guards_injective]
  simp

/-- Dense Boolean incidence representation: food, inputs, outputs, catalysis,
and k listed-set rows. Dimension headers are supplied separately in unary. -/
def encodingCells (k n : Nat) : Nat :=
  Fintype.card (Mol k n) +
  (3 * Fintype.card (Mol k n) + k) * Fintype.card (Rxn k n)

/-- An explicit polynomial, including k as a parameter factor. -/
theorem encoding_polynomial : encodingCells k n =
    (2 + 2*(k*(n+2)) + k + (k*(n+2))^2) +
    (3*(2 + 2*(k*(n+2)) + k + (k*(n+2))^2)+k) *
    (2*(k*(n+2)) + 2*(k*(n+2))^2 + 1) := by
  simp only [encodingCells,molecule_count,reaction_count]

end AllIrrRAFCert.Hardness
