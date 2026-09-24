import proofs.AllIrrRAFCert.Hardness.EncodingSize

namespace AllIrrRAFCert.Hardness

variable {k n : Nat}

/-- One bit for each food membership, each of three molecule/reaction
incidence matrices, and each of k supplied reaction-set membership rows. -/
abbrev EncodingIndex (k n : Nat) :=
  Mol k n ⊕ (Fin 3 × Mol k n × Rxn k n) ⊕ (Fin k × Rxn k n)

def catBool : Mol k n → Rxn k n → Bool
  | .globalCat, _ => true
  | .guardCat u, .selector v => decide (u = next v)
  | _, _ => false

@[simp] theorem catBool_iff (x : Mol k n) (r : Rxn k n) : catBool x r = true ↔ cat x r := by
  cases x <;> cases r <;> simp [catBool,cat]

/-- Explicit, computable Boolean output encoding. It queries `bad` only in
the input rows of pair gates; every other bit follows the fixed source rules. -/
def encode (bad : Pair k n → Bool) : EncodingIndex k n → Bool
  | .inl x => decide (x ∈ (crs bad).food)
  | .inr (.inl (j,x,r)) =>
      if j.val = 0 then decide (x ∈ (crs bad).inputs r)
      else if j.val = 1 then decide (x ∈ (crs bad).outputs r)
      else catBool x r
  | .inr (.inr (i,r)) => decide (r ∈ guard i)

theorem encode_food (bad : Pair k n → Bool) (x : Mol k n) :
    encode bad (.inl x) = true ↔ x ∈ (crs bad).food := by simp [encode]

theorem encode_inputs (bad : Pair k n → Bool) (x : Mol k n) (r : Rxn k n) :
    encode bad (.inr (.inl (0,x,r))) = true ↔ x ∈ (crs bad).inputs r := by
  simp [encode]

theorem encode_outputs (bad : Pair k n → Bool) (x : Mol k n) (r : Rxn k n) :
    encode bad (.inr (.inl (1,x,r))) = true ↔ x ∈ (crs bad).outputs r := by
  simp [encode]

theorem encode_catalysis (bad : Pair k n → Bool) (x : Mol k n) (r : Rxn k n) :
    encode bad (.inr (.inl (2,x,r))) = true ↔ cat x r := by simp [encode]

theorem encode_list (bad : Pair k n → Bool) (i : Fin k) (r : Rxn k n) :
    encode bad (.inr (.inr (i,r))) = true ↔ r ∈ guard i := by simp [encode]

theorem encoding_card : Fintype.card (EncodingIndex k n) = encodingCells k n := by
  simp only [EncodingIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,encodingCells]
  ring

end AllIrrRAFCert.Hardness
