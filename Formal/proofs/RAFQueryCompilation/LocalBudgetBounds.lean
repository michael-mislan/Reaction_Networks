import proofs.RAFQueryCompilation.BudgetLocal

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

theorem budgetLocal_complete (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M) (oldMask availableMask : R → Bool)
    (D E : Finset R) (counts : M → ℕ) (cert : List (List R)) (budget : ℕ)
    (h : (cappedLocal Q cats succ needs oldMask availableMask D E counts cert).2 ≤ budget) :
    budgetLocal Q cats succ needs oldMask availableMask D E counts cert budget =
      cappedLocal Q cats succ needs oldMask availableMask D E counts cert := by
  let md := collectRegionalMetadata Q cats succ needs E
  let regionFee := metadataCharge E+metadataRegionCharge md D E
  let prepared := regionFee+metadataBoundaryCharge md Q.food.card E.card
  by_cases hr : checkRegion succ D E
  · have hb : prepared ≤ budget := by
      simp only [cappedLocal, if_pos hr] at h
      change prepared+_ ≤ budget at h
      omega
    have hp : regionFee ≤ budget := (Nat.le_add_right _ _).trans hb
    have hm : metadataCharge E ≤ budget := (Nat.le_add_right _ _).trans hp
    have hi : (cappedPruning (withFood Q (maskFood Q needs E oldMask counts)) cats
        md.inputArity md.outputArity md.catalystArity (maskRegion E availableMask) cert).2 ≤
          budget-prepared := by
      simp only [cappedLocal, if_pos hr] at h
      change prepared+_ ≤ budget at h
      dsimp only [md]
      omega
    have hc := budgetPruning_complete (withFood Q (maskFood Q needs E oldMask counts)) cats
      md.inputArity md.outputArity md.catalystArity (maskRegion E availableMask) cert
      (budget-prepared) hi
    dsimp only [prepared, regionFee, md] at hp hb hc
    simp only [budgetLocal, if_pos hm, if_pos hp, if_pos hr, if_pos hb,
      hc, cappedLocal]
  · have hp : regionFee ≤ budget := by simpa only [cappedLocal, if_neg hr] using h
    have hm : metadataCharge E ≤ budget := (Nat.le_add_right _ _).trans hp
    dsimp only [regionFee, md] at hp
    simp only [budgetLocal, if_pos hm, if_pos hp, if_neg hr, cappedLocal]

/-- A source/region/certificate bound; it does not inspect the resulting RAF. -/
def localSourceCap (Q : CRS M R) (cats : R → Finset M) (succ : R → Finset R)
    (needs : R → Finset M) (D E : Finset R) (cert : List (List R)) : ℕ :=
  let md := collectRegionalMetadata Q cats succ needs E
  let p := (sourceEnvelope Q needs E).card
  metadataCharge E+regionCharge succ D E+boundaryCharge Q needs E+
    cert.flatten.length*replayCap E.card md.inputArity md.outputArity p+
    (E.card+1)*pruningRoundCap E.card md.inputArity md.outputArity md.catalystArity p

theorem cappedLocal_source_bound (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M) (oldMask availableMask : R → Bool)
    (D E : Finset R) (counts : M → ℕ) (cert : List (List R)) :
    (cappedLocal Q cats succ needs oldMask availableMask D E counts cert).2 ≤
      localSourceCap Q cats succ needs D E cert := by
  let md := collectRegionalMetadata Q cats succ needs E
  have ha := metadata_arities Q cats succ needs E
  have hsub : maskRegion E availableMask ⊆ E := Finset.filter_subset _ _
  have hf : maskFood Q needs E oldMask counts ⊆ sourceEnvelope Q needs E :=
    (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.filter_subset _ _)).trans Finset.subset_union_left
  have hout : ∀ r ∈ maskRegion E availableMask,
      (withFood Q (maskFood Q needs E oldMask counts)).outputs r ⊆ sourceEnvelope Q needs E := by
    intro r hr x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,hsub hr,hx⟩)
  have hb := cappedPruning_source_bound
    (withFood Q (maskFood Q needs E oldMask counts)) cats (sourceEnvelope Q needs E)
    E.card md.inputArity md.outputArity md.catalystArity hf cert
    (maskRegion E availableMask) (Finset.card_le_card hsub)
    (fun r hr => (ha r (hsub hr)).1) (fun r hr => (ha r (hsub hr)).2.1) hout
  unfold cappedLocal localSourceCap
  split
  · simp only [metadata_region_exact, metadata_boundary_exact]
    simpa only [Nat.add_assoc] using Nat.add_le_add_left hb
      (metadataCharge E+regionCharge succ D E+boundaryCharge Q needs E)
  · simp only [metadata_region_exact, Nat.add_assoc]
    omega

theorem budgetLocal_source_complete (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M) (oldMask availableMask : R → Bool)
    (D E : Finset R) (counts : M → ℕ) (cert : List (List R)) (budget : ℕ)
    (h : localSourceCap Q cats succ needs D E cert ≤ budget) :
    budgetLocal Q cats succ needs oldMask availableMask D E counts cert budget =
      cappedLocal Q cats succ needs oldMask availableMask D E counts cert :=
  budgetLocal_complete Q cats succ needs oldMask availableMask D E counts cert budget
    ((cappedLocal_source_bound Q cats succ needs oldMask availableMask D E counts cert).trans h)

end RAFQueryCompilation
