import proofs.CompositionalMemory.GenericCountReaction

namespace CompositionalMemory

abbrev GeneralReactionChannel (k : ℕ) (R : Type*) := (Fin k × R) ⊕ ((Fin k × Fin k) ⊕ Fin k)

def speciesUnit {d : ℕ} (z : Fin d) : Fin d → ℕ := fun j => if j=z then 1 else 0

def generalResidentNext {k d : ℕ} (s : GeneralCountState k d) (i : Fin k)
    (consume produce : Fin d → ℕ) : GeneralCountState k d :=
  (Function.update s.1 i (countReactionNext consume produce (s.1 i)),s.2)

def generalExchangeNext {k d : ℕ} (z : Fin d) (s : GeneralCountState k d)
    (i j : Fin k) : GeneralCountState k d :=
  if i=j ∨ s.1 i z=0 then s else
    (Function.update (Function.update s.1 i (countReactionNext (speciesUnit z) (fun _ => 0) (s.1 i)))
      j (countReactionNext (fun _ => 0) (speciesUnit z) (s.1 j)),s.2)

def generalMembraneNext {k d : ℕ} (z : Fin d) (s : GeneralCountState k d)
    (i : Fin k) : GeneralCountState k d :=
  if s.1 i z=0 then s else
    (Function.update s.1 i (countReactionNext (speciesUnit z) (fun _ => 0) (s.1 i)),s.2+1)

def generalGlobalNext {k d : ℕ} {R : Type*} (consume produce : Fin k → R → Fin d → ℕ)
    (z : Fin d) (s : GeneralCountState k d) : GeneralReactionChannel k R → GeneralCountState k d :=
  Sum.elim (fun ir => generalResidentNext s ir.1 (consume ir.1 ir.2) (produce ir.1 ir.2))
    (Sum.elim (fun ij => generalExchangeNext z s ij.1 ij.2) (fun i => generalMembraneNext z s i))

noncomputable def generalGlobalRate {k d : ℕ} {R : Type*}
    (consume : Fin k → R → Fin d → ℕ) (coeff : Fin k → R → ℝ)
    (z : Fin d) (γ : ℝ) (w : Fin k → Fin k → ℝ) (s : GeneralCountState k d) :
    GeneralReactionChannel k R → ℝ :=
  Sum.elim (fun ir => ((s.2:ℝ)/k)*countReactionDensity (coeff ir.1 ir.2) ((s.2:ℝ)/k)
      (consume ir.1 ir.2) (s.1 ir.1))
    (Sum.elim (fun ij => w ij.1 ij.2*(s.1 ij.1 z:ℝ)) (fun i => γ*(s.1 i z:ℝ)))

theorem general_global_rate_nonneg {k d : ℕ} {R : Type*}
    (consume : Fin k → R → Fin d → ℕ) (coeff : Fin k → R → ℝ)
    (z : Fin d) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hc : ∀ i r, 0 ≤ coeff i r) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (s : GeneralCountState k d) (r : GeneralReactionChannel k R) :
    0 ≤ generalGlobalRate consume coeff z γ w s r := by
  rcases r with ir | r
  · exact mul_nonneg (by positivity)
      (count_reaction_density_nonneg _ _ _ _ (hc ir.1 ir.2) (by positivity))
  · rcases r with ij | i
    · exact mul_nonneg (hw ij.1 ij.2) (Nat.cast_nonneg _)
    · exact mul_nonneg hγ (Nat.cast_nonneg _)

theorem general_global_membrane_step {k d : ℕ} {R : Type*}
    (consume produce : Fin k → R → Fin d → ℕ) (z : Fin d)
    (s : GeneralCountState k d) (r : GeneralReactionChannel k R) :
    s.2 ≤ (generalGlobalNext consume produce z s r).2 ∧
      (generalGlobalNext consume produce z s r).2 ≤ s.2+1 := by
  rcases r with ir | r
  · simp [generalGlobalNext,generalResidentNext]
  · rcases r with ij | i
    · simp only [generalGlobalNext,Sum.elim_inr,Sum.elim_inl,generalExchangeNext]
      split_ifs <;> simp
    · simp only [generalGlobalNext,Sum.elim_inr,generalMembraneNext]
      split_ifs <;> simp

end CompositionalMemory
