import proofs.RAFQueryCompilation.RegionalMetadata
import proofs.RAFQueryCompilation.CappedBounds

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def cappedLocal (Q : CRS M R) (cats : R → Finset M) (succ : R → Finset R)
    (needs : R → Finset M) (oldMask availableMask : R → Bool) (D E : Finset R)
    (counts : M → ℕ) (cert : List (List R)) : Option (Finset R) × ℕ :=
  let md := collectRegionalMetadata Q cats succ needs E
  let regionFee := metadataCharge E+metadataRegionCharge md D E
  if checkRegion succ D E then
    let prepared := regionFee+metadataBoundaryCharge md Q.food.card E.card
    let inner := cappedPruning (withFood Q (maskFood Q needs E oldMask counts)) cats
      md.inputArity md.outputArity md.catalystArity (maskRegion E availableMask) cert
    (inner.1,prepared+inner.2)
  else (none,regionFee)

/-- Metadata, region validation and boundary creation are each prepaid.
Only then does the budgeted certificate consumer receive the residual budget. -/
def budgetLocal (Q : CRS M R) (cats : R → Finset M) (succ : R → Finset R)
    (needs : R → Finset M) (oldMask availableMask : R → Bool) (D E : Finset R)
    (counts : M → ℕ) (cert : List (List R)) (budget : ℕ) : Option (Finset R) × ℕ :=
  if metadataCharge E ≤ budget then
    let md := collectRegionalMetadata Q cats succ needs E
    let regionFee := metadataCharge E+metadataRegionCharge md D E
    if regionFee ≤ budget then
      if checkRegion succ D E then
        let prepared := regionFee+metadataBoundaryCharge md Q.food.card E.card
        if prepared ≤ budget then
          let inner := budgetPruning (withFood Q (maskFood Q needs E oldMask counts)) cats
            md.inputArity md.outputArity md.catalystArity (maskRegion E availableMask)
            cert (budget-prepared)
          (inner.1,prepared+inner.2)
        else (none,regionFee)
      else (none,regionFee)
    else (none,metadataCharge E)
  else (none,0)

theorem budgetLocal_bound (Q : CRS M R) (cats : R → Finset M) (succ : R → Finset R)
    (needs : R → Finset M) (oldMask availableMask : R → Bool) (D E : Finset R)
    (counts : M → ℕ) (cert : List (List R)) (budget : ℕ) :
    (budgetLocal Q cats succ needs oldMask availableMask D E counts cert budget).2 ≤ budget := by
  let md := collectRegionalMetadata Q cats succ needs E
  have hi := budgetPruning_bound (withFood Q (maskFood Q needs E oldMask counts)) cats
    md.inputArity md.outputArity md.catalystArity (maskRegion E availableMask) cert
    (budget-(metadataCharge E+metadataRegionCharge md D E+
      metadataBoundaryCharge md Q.food.card E.card))
  dsimp only [md] at hi
  dsimp only [budgetLocal]
  split_ifs <;> simp_all only <;> omega

theorem cappedLocal_refines [Fintype M] (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M) (oldMask availableMask : R → Bool)
    (D E : Finset R) (counts : M → ℕ) (cert : List (List R)) :
    (cappedLocal Q cats succ needs oldMask availableMask D E counts cert).1 =
      checkMaskedLocal Q (fun x r => x ∈ cats r) succ needs oldMask availableMask D E counts cert := by
  simp only [cappedLocal, checkMaskedLocal]
  split
  · exact cappedPruning_refines _ cats _ _ _ cert _
  · rfl

theorem budgetLocal_refines [Fintype M] (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M) (oldMask availableMask : R → Bool)
    (D E : Finset R) (counts : M → ℕ) (cert : List (List R)) (budget : ℕ)
    {answer : Finset R}
    (h : (budgetLocal Q cats succ needs oldMask availableMask D E counts cert budget).1 = some answer) :
    checkMaskedLocal Q (fun x r => x ∈ cats r) succ needs oldMask availableMask D E counts cert =
      some answer := by
  dsimp only [budgetLocal] at h
  split at h
  · split at h
    · split at h
      · rename_i hr
        split at h
        · simp only [checkMaskedLocal, if_pos hr]
          exact budgetPruning_refines _ cats _ _ _ _ cert _ h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

end RAFQueryCompilation
