import proofs.RAFQueryCompilation.SparseCertificate

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def maskRegion (E : Finset R) (mask : R → Bool) : Finset R :=
  E.filter (fun r => mask r)

theorem maskRegion_eq (E S : Finset R) (mask : R → Bool)
    (hm : ∀ r, mask r = true ↔ r ∈ S) :
    maskRegion E mask = restrictToRegion E S := by
  ext r
  simp only [maskRegion, restrictToRegion, Finset.mem_filter, hm]

def maskFood (Q : CRS M R) (needs : R → Finset M) (E : Finset R)
    (oldMask : R → Bool) (counts : M → ℕ) : Finset M :=
  Q.food ∪ (E.biUnion needs).filter
    (fun x => producerCount Q (maskRegion E oldMask) x < counts x)

variable [Fintype M]
def checkMaskedLocal (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R) (needs : R → Finset M)
    (oldMask availableMask : R → Bool) (D E : Finset R)
    (counts : M → ℕ) (certificate : List (List R)) : Option (Finset R) :=
  if checkRegion succ D E then
    checkPruning (withFood Q (maskFood Q needs E oldMask counts)) C
      (maskRegion E availableMask) certificate
  else none

theorem checkMaskedLocal_sound (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R) (needs : R → Finset M)
    (hi : IndexSound Q C succ) (hn : NeedsSound Q C needs)
    (A B D E : Finset R) (counts : M → ℕ) (certificate : List (List R))
    (oldMask availableMask : R → Bool)
    (ho : ∀ r, oldMask r = true ↔ r ∈ evaluate Q C A)
    (ha : ∀ r, availableMask r = true ↔ r ∈ B)
    (hcounts : ∀ x, counts x = producerCount Q (evaluate Q C A) x)
    (hedits : ∀ r, (r ∈ A ↔ r ∈ B) ∨ r ∈ D) {localAnswer : Finset R}
    (h : checkMaskedLocal Q C succ needs oldMask availableMask D E counts certificate =
      some localAnswer) :
    evaluate Q C B = (evaluate Q C A \ E) ∪ localAnswer := by
  have hcheck : checkMaskedLocal Q C succ needs oldMask availableMask D E counts certificate =
      checkSparseLocal Q C succ needs (evaluate Q C A) B D E counts certificate := by
    simp only [checkMaskedLocal, checkSparseLocal, maskFood, sparseFood,
      maskRegion_eq E _ oldMask ho, maskRegion_eq E B availableMask ha]
  rw [hcheck] at h
  exact checkSparseLocal_sound Q C succ needs hi hn A B D E counts certificate
    hcounts hedits h

/-- Array-backed masks have a literal finite-set interpretation used only in proofs. -/
def maskSet {n : ℕ} (mask : Vector Bool n) : Finset (Fin n) :=
  Finset.univ.filter (fun r => mask[r.val])

theorem vectorMask_refines {n : ℕ} (mask : Vector Bool n) (r : Fin n) :
    mask[r.val] = true ↔ r ∈ maskSet mask := by
  simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]

end RAFQueryCompilation
