import proofs.AllIrrRAFCert.WPHardness.Reduction

namespace AllIrrRAFCert.WPHardness

variable {k n q : Nat}

/-- One bit for each food membership, each of three molecule/reaction
incidence matrices, and each of k supplied reaction-set membership rows. -/
abbrev EncodingIndex (k n q : Nat) :=
  Mol k n ⊕ (Fin 3 × Mol k n × Rxn k n q) ⊕ (Fin k × Rxn k n q)

def catBool : Mol k n → Rxn k n q → Bool
  | .globalCat, _ => true
  | .guardCat u, .selector v => decide (u = next v)
  | _, _ => false

@[simp] theorem catBool_iff (x : Mol k n) (r : Rxn k n q) : catBool x r = true ↔ cat x r := by
  cases x <;> cases r <;> simp [catBool,cat]

/-- Explicit, computable Boolean output encoding. Every row is obtained directly from the literal finite source rules. -/
def encode (A : System n q) : EncodingIndex k n q → Bool
  | .inl x => decide (x ∈ (crs A).food)
  | .inr (.inl (j,x,r)) =>
      if j.val = 0 then decide (x ∈ (crs A).inputs r)
      else if j.val = 1 then decide (x ∈ (crs A).outputs r)
      else catBool x r
  | .inr (.inr (i,r)) => decide (r ∈ guard i)

theorem encode_food (A : System n q) (x : Mol k n) :
    encode A (.inl x) = true ↔ x ∈ (crs A).food := by simp [encode]

theorem encode_inputs (A : System n q) (x : Mol k n) (r : Rxn k n q) :
    encode A (.inr (.inl (0,x,r))) = true ↔ x ∈ (crs A).inputs r := by
  simp [encode]

theorem encode_outputs (A : System n q) (x : Mol k n) (r : Rxn k n q) :
    encode A (.inr (.inl (1,x,r))) = true ↔ x ∈ (crs A).outputs r := by
  simp [encode]

theorem encode_catalysis (A : System n q) (x : Mol k n) (r : Rxn k n q) :
    encode A (.inr (.inl (2,x,r))) = true ↔ cat x r := by simp [encode]

theorem encode_list (A : System n q) (i : Fin k) (r : Rxn k n q) :
    encode A (.inr (.inr (i,r))) = true ↔ r ∈ guard i := by simp [encode]

theorem encoding_card : Fintype.card (EncodingIndex k n q) = encodingCells k n q := by
  simp only [EncodingIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,encodingCells]
  ring

end AllIrrRAFCert.WPHardness
