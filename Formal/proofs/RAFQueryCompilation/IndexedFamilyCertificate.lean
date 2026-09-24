import proofs.RAFQueryCompilation.IndexedFamily

namespace RAFQueryCompilation.ModuleFamily
open RAF

theorem indexed_certificate_accepts {n : ℕ} (i : Fin n)
    (food : Finset (Fin (n*2+1+1))) (A : Finset (Fin (n*2+1)))
    (hA : A ⊆ indexedRegion i) :
    ∃ L, checkPruning {indexedSource n with food := food}
      (fun x r => x ∈ indexedCats n r) A (indexedCertificate i) = some L := by
  let a := reactionCode n (some (i,false))
  let b := reactionCode n (some (i,true))
  have hab : a ≠ b := by simp [a,b]
  have he : A = (if a ∈ A then {a} else ∅) ∪ (if b ∈ A then {b} else ∅) := by
    ext r
    by_cases hr₁ : r = a
    · subst r
      by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [ha,hb,hab]
    · by_cases hr₂ : r = b
      · subst r
        by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [ha,hb,hr₁]
      · have hn : r ∉ A := by
          intro h
          have hmem : r = a ∨ r = b := by simpa [indexedRegion,region] using hA h
          exact hmem.elim hr₁ hr₂
        by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [ha,hb,hn,hr₁,hr₂]
  rw [he]
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;>
    by_cases hh : moleculeCode n (some none) ∈ food <;>
    by_cases hl : moleculeCode n (some (some (i,false))) ∈ food <;>
    by_cases hr : moleculeCode n (some (some (i,true))) ∈ food <;>
    simp [ha,hb,hh,hl,hr,a,b,indexedCertificate,pairCertificate,checkPruning,checkClosure,
      replaySchedule,scheduleStep,closureStep,Enabled,pruneWithPool,indexedSource,indexedCats,source,familyCats]

theorem indexed_region_accepts {n : ℕ} (i : Fin n) (D : Finset (Fin (n*2+1)))
    (hd : D ⊆ indexedRegion i) :
    checkRegion (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r)) D
      (indexedRegion i) = true := by
  simp only [checkRegion, decide_eq_true_eq]
  refine ⟨hd, ?_⟩
  intro r hr s hs
  simp only [indexedRegion,region,Finset.map_insert,Finset.map_singleton,
    Finset.mem_insert,Finset.mem_singleton,Equiv.toEmbedding_apply] at hr
  rcases hr with hr | hr <;> subst r <;> rw [indexed_successors] at hs <;>
    simp only [Finset.mem_singleton] at hs <;> subst s <;> simp [indexedRegion,region]

theorem indexed_local_accepts {n : ℕ} (i : Fin n) (D : Finset (Fin (n*2+1)))
    (hd : D ⊆ indexedRegion i) (oldMask availableMask : Fin (n*2+1) → Bool)
    (counts : Fin (n*2+1+1) → ℕ) :
    ∃ L, checkMaskedLocal (indexedSource n) (fun x r => x ∈ indexedCats n r)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r))
      oldMask availableMask D (indexedRegion i) counts (indexedCertificate i) = some L := by
  unfold checkMaskedLocal
  rw [indexed_region_accepts i D hd]
  exact indexed_certificate_accepts i _ _ (Finset.filter_subset _ _)

end RAFQueryCompilation.ModuleFamily
