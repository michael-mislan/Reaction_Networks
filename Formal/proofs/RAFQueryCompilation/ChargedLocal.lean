import proofs.RAFQueryCompilation.ChargedPruning

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Source-index charge, including conservative extra successor entries. -/
def regionCharge (succ : R → Finset R) (D E : Finset R) : ℕ :=
  1 + (D.card+E.card+(∑ r ∈ E, (succ r).card))*(E.card+1)

/-- Declared list-primitive boundary budget. Needed-list unions and repeated
local producer counts are charged; vector/count lookups are RAM primitives. -/
def boundaryCharge (Q : CRS M R) (needs : R → Finset M) (E : Finset R) : ℕ :=
  let n := ∑ r ∈ E, (needs r).card
  let o := ∑ r ∈ E, (Q.outputs r).card
  1 + (Q.food.card+n+E.card+1)^2 + (n+1)*(E.card+1)*(o+E.card+2)

def chargedLocal (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M)
    (oldMask availableMask : R → Bool) (D E : Finset R)
    (counts : M → ℕ) (certificate : List (List R)) : Option (Finset R) × ℕ :=
  if checkRegion succ D E then
    let inner := chargedPruning (withFood Q (maskFood Q needs E oldMask counts)) cats
      (maskRegion E availableMask) certificate
    (inner.1, regionCharge succ D E + boundaryCharge Q needs E + inner.2)
  else (none, regionCharge succ D E)

theorem chargedLocal_refines [Fintype M] (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M)
    (oldMask availableMask : R → Bool) (D E : Finset R)
    (counts : M → ℕ) (certificate : List (List R)) :
    (chargedLocal Q cats succ needs oldMask availableMask D E counts certificate).1 =
      checkMaskedLocal Q (fun x r => x ∈ cats r) succ needs oldMask availableMask
        D E counts certificate := by
  simp only [chargedLocal, checkMaskedLocal]
  split
  · exact chargedPruning_refines _ _ _ _
  · rfl

/-- Complete local-consumer charge in the declared model. All parameters on
the right are source/region/certificate inputs, independent of the new answer. -/
theorem chargedLocal_bound (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M)
    (oldMask availableMask : R → Bool) (D E : Finset R)
    (counts : M → ℕ) (certificate : List (List R)) (i o c : ℕ)
    (hi : ∀ r ∈ E, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ E, (Q.outputs r).card ≤ o)
    (hc : ∀ r ∈ E, (cats r).card ≤ c) :
    (chargedLocal Q cats succ needs oldMask availableMask D E counts certificate).2 ≤
      regionCharge succ D E + boundaryCharge Q needs E +
      certificate.flatten.length * replayCap E.card i o (sourceEnvelope Q needs E).card +
      (E.card+1) * pruningRoundCap E.card i o c (sourceEnvelope Q needs E).card := by
  have hsub : maskRegion E availableMask ⊆ E := Finset.filter_subset _ _
  have hf : maskFood Q needs E oldMask counts ⊆ sourceEnvelope Q needs E := by
    exact (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.filter_subset _ _)).trans Finset.subset_union_left
  have hout : ∀ r ∈ maskRegion E availableMask,
      (withFood Q (maskFood Q needs E oldMask counts)).outputs r ⊆ sourceEnvelope Q needs E := by
    intro r hr x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,hsub hr,hx⟩)
  have hb := chargedPruning_source_bound
    (withFood Q (maskFood Q needs E oldMask counts)) cats (sourceEnvelope Q needs E)
    E.card i o c hf certificate (maskRegion E availableMask) (Finset.card_le_card hsub)
    (fun r hr => hi r (hsub hr)) (fun r hr => ho r (hsub hr))
    (fun r hr => hc r (hsub hr)) hout
  unfold chargedLocal
  split
  · simpa only [Nat.add_assoc] using
      Nat.add_le_add_left hb (regionCharge succ D E + boundaryCharge Q needs E)
  · simp only [Nat.add_assoc]
    exact Nat.le_add_right _ _

end RAFQueryCompilation
