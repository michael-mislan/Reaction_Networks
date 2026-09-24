import proofs.RAFQueryCompilation.MaskCertificate

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def editedMask (base : R → Bool) (removed added : Finset R) (r : R) : Bool :=
  (base r && !(decide (r ∈ removed))) || decide (r ∈ added)

theorem editedMask_correct (base : R → Bool) (A removed added : Finset R)
    (ha : ∀ r, base r = true ↔ r ∈ A) (r : R) :
    editedMask base removed added r = true ↔ r ∈ (A \ removed) ∪ added := by
  simp [editedMask, ha]

theorem reference_edit_cover (A removed added : Finset R) :
    ∀ r, (r ∈ A ↔ r ∈ (A \ removed) ∪ added) ∨ r ∈ removed ∪ added := by
  intro r
  by_cases hm : r ∈ removed
  · exact Or.inr (Finset.mem_union_left _ hm)
  by_cases hp : r ∈ added
  · exact Or.inr (Finset.mem_union_right _ hp)
  · exact Or.inl (by simp [hm, hp])

variable [Fintype M]
theorem checkReferenceEdit_sound (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R) (needs : R → Finset M)
    (hi : IndexSound Q C succ) (hn : NeedsSound Q C needs)
    (A removed added E : Finset R) (counts : M → ℕ) (certificate : List (List R))
    (oldMask baseMask : R → Bool)
    (ho : ∀ r, oldMask r = true ↔ r ∈ evaluate Q C A)
    (ha : ∀ r, baseMask r = true ↔ r ∈ A)
    (hcounts : ∀ x, counts x = producerCount Q (evaluate Q C A) x)
    {localAnswer : Finset R}
    (h : checkMaskedLocal Q C succ needs oldMask (editedMask baseMask removed added)
      (removed ∪ added) E counts certificate = some localAnswer) :
    evaluate Q C ((A \ removed) ∪ added) = (evaluate Q C A \ E) ∪ localAnswer := by
  exact checkMaskedLocal_sound Q C succ needs hi hn A _ _ E counts certificate oldMask _
    ho (editedMask_correct baseMask A removed added ha) hcounts
    (reference_edit_cover A removed added) h

end RAFQueryCompilation
