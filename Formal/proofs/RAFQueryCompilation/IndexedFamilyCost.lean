import proofs.RAFQueryCompilation.IndexedFamilyCertificate

namespace RAFQueryCompilation.ModuleFamily
open RAF

theorem indexed_metadata {n : ℕ} (i : Fin n) :
    collectRegionalMetadata (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) (indexedRegion i) =
      ⟨2,4,2,1,1,1⟩ := by
  simp [collectRegionalMetadata,indexedRegion,region,indexed_successors,indexed_needs]

theorem indexed_region_charge {n : ℕ} (i : Fin n) (D : Finset (Fin (n*2+1)))
    (hd : D ⊆ indexedRegion i) :
    regionCharge (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      D (indexedRegion i) ≤ 19 := by
  have hc := Finset.card_le_card hd
  rw [indexed_region_card] at hc
  rw [← metadata_region_exact (indexedSource n) (indexedCats n) _
    (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)),indexed_metadata]
  simp only [metadataRegionCharge,indexed_region_card]
  omega

theorem indexed_boundary_charge {n : ℕ} (i : Fin n) :
    boundaryCharge (indexedSource n)
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) (indexedRegion i) = 155 := by
  rw [← metadata_boundary_exact (indexedSource n) (indexedCats n)
    (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r)),indexed_metadata]
  simp [metadataBoundaryCharge]

theorem indexed_local_cap {n : ℕ} (i : Fin n) (D : Finset (Fin (n*2+1)))
    (hd : D ⊆ indexedRegion i) :
    localSourceCap (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r))
      D (indexedRegion i) (indexedCertificate i) ≤ 831 := by
  have hg := indexed_region_charge i D hd
  unfold localSourceCap
  rw [indexed_metadata,indexed_envelope_card,indexed_boundary_charge]
  simp only [metadataCharge,indexed_region_card,indexedCertificate,pairCertificate,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.length_cons,List.length_nil,replayCap,pruningRoundCap]
  omega

theorem indexed_query_cap {n : ℕ} (i : Fin n) (removed added : Finset (Fin (n*2+1)))
    (hd : removed ∪ added ⊆ indexedRegion i) :
    querySourceCap (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r))
      removed added (indexedRegion i) (indexedCertificate i) ≤ 1011 := by
  have hr := Finset.card_le_card (Finset.subset_union_left.trans hd)
  have ha := Finset.card_le_card (Finset.subset_union_right.trans hd)
  rw [indexed_region_card] at hr ha
  have hp : editPrepCharge removed added ≤ 26 := by
    have h := Nat.pow_le_pow_left (by omega : removed.card+added.card+1 ≤ 5) 2
    dsimp only [editPrepCharge]
    omega
  have hl := indexed_local_cap i (removed ∪ added) hd
  unfold querySourceCap
  rw [indexed_metadata]
  simp only [metadataCharge,indexed_region_card,metadataStateCap]
  omega

/-- The existing indexed transaction succeeds with a constant budget on every
pair edit, without assuming anything about boundary food or old availability. -/
theorem indexed_transaction_accepts {n : ℕ} (i : Fin n)
    (state : QueryState (n*2+1+1) (n*2+1)) (removed added : Finset (Fin (n*2+1)))
    (hd : removed ∪ added ⊆ indexedRegion i) :
    ∃ L, (budgetQuery (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) state
      removed added (indexedRegion i) (indexedCertificate i) 1011).answer = some L := by
  obtain ⟨L,hL⟩ := indexed_local_accepts i (removed ∪ added) hd
    (fun r => state.answer[r.val]) (editedMask (fun r => state.available[r.val]) removed added)
    (fun x => state.counts[x.val])
  exact ⟨L,budgetQuery_source_complete _ _ _ _ state removed added _ _ 1011
    (indexed_query_cap i removed added hd) hL⟩

theorem indexed_hybrid_charge {n : ℕ} (i : Fin n)
    (state : QueryState (n*2+1+1) (n*2+1)) (removed added : Finset (Fin (n*2+1)))
    (hd : removed ∪ added ⊆ indexedRegion i) :
    (hybridQuery (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) state
      removed added (indexedRegion i) (indexedCertificate i) 1011).2 ≤ 1012 := by
  obtain ⟨L,hL⟩ := indexed_transaction_accepts i state removed added hd
  have hb := budgetQuery_bound (indexedSource n) (indexedCats n)
    (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
    (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) state
    removed added (indexedRegion i) (indexedCertificate i) 1011
  simp only [hybridQuery,hL]
  omega

end RAFQueryCompilation.ModuleFamily
