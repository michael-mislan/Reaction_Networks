import proofs.RAF.Frankl.LocalRankedClosure
namespace RAF.Frankl
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

theorem localSupplierFibre_average (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank)
    (T : Finset R) (hU : SupplierCore Q C U) :
    (extensionFibre Q C U T).card * Fintype.card {r // r ∈ U} ≤
      2 * ∑ S ∈ extensionFibre Q C U T, S.card := by
  classical
  let d : {r // r ∈ U} → {r // r ∈ U} := fun r =>
    ⟨Classical.choose (hU.2 r.1 r.2), (Classical.choose_spec (hU.2 r.1 r.2)).1⟩
  have hd : ∀ r, CompleteSupplier Q C (d r).1 r.1 :=
    fun r => (Classical.choose_spec (hU.2 r.1 r.2)).2
  let L := fun (r : {r // r ∈ U}) (S : Finset {r // r ∈ U}) =>
    LocalSupply Q C (fromRestricted S ∪ T) r.1
  have hm : ∀ {A B : Finset {r // r ∈ U}}, A ⊆ B →
      fromRestricted A ∪ T ⊆ fromRestricted B ∪ T :=
    fun hab => Finset.union_subset_union (fromRestricted_mono hab) (Finset.Subset.refl T)
  have h := CommonSupplier.supported_upward_average L d
    (fun _ {_ _} hab => localSupply_mono Q C (hm hab))
    (fun r S hs => completeSupplier_local Q C (hd r)
      (Finset.mem_union_left _ ((mem_fromRestricted S (d r).1).mpr ⟨(d r).2,hs⟩)))
    (closureExterior Q C U T)
    (fun hab => closureExterior_mono Q C U T hab)
  have heq : extensionFibre Q C U T = Finset.univ.powerset.filter
      (fun S => closureExterior Q C U T S ∧ ∀ r ∈ S, L r S) := by
    ext S
    simp only [extensionFibre,Finset.mem_filter,local_rank_fibre_iff Q C U rank hrank,L]
  rw [heq]
  exact h

/-- Literal source theorem: a ranked ordinary CRS with a complete-supplier core
has an empty-inclusive globally abundant reaction in that core. -/
theorem local_supplier_core_exists_abundant (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank) (hU : SupplierCore Q C U) :
    ∃ r ∈ U, (fixedFamily Q C).card ≤
      2 * ((fixedFamily Q C).filter (fun W => r ∈ W)).card := by
  classical
  have hn : Nonempty {r // r ∈ U} := by
    obtain ⟨r,hr⟩ := hU.1
    exact ⟨⟨r,hr⟩⟩
  letI := hn
  apply Exists.elim (exists_frequency_of_fibre_average
    (fixedFamily Q C) (toRestricted U) (fun W => W \ U) ?_)
  · intro r hr
    exact ⟨r.1,r.2,by simpa using hr⟩
  · intro T
    by_cases hT : Disjoint T U
    · have h := localSupplierFibre_average Q C U rank hrank T hU
      rw [← core_fibre_image Q C U T hT] at h
      rw [Finset.card_image_iff.mpr (core_restrict_injOn Q C U T),
        Finset.sum_image (core_restrict_injOn Q C U T)] at h
      exact h
    · have he : (fixedFamily Q C).filter (fun W => W \ U = T) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro W hw
        have ht := (Finset.mem_filter.mp hw).2
        apply hT
        rw [← ht]
        exact Finset.sdiff_disjoint
      simp [he]

/-- The aggregate global core occupancy, retaining every exterior multiplicity. -/
theorem local_supplier_core_global_average (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank) (hU : SupplierCore Q C U) :
    (fixedFamily Q C).card * U.card ≤
      2 * ∑ W ∈ fixedFamily Q C, (W ∩ U).card := by
  classical
  let F := fixedFamily Q C
  have h : ∀ T : Finset R,
      (F.filter (fun W => W \ U = T)).card * Fintype.card {r // r ∈ U} ≤
        2 * ∑ W ∈ F.filter (fun W => W \ U = T), (toRestricted U W).card := by
    intro T
    by_cases hT : Disjoint T U
    · have hh := localSupplierFibre_average Q C U rank hrank T hU
      rw [← core_fibre_image Q C U T hT] at hh
      rw [Finset.card_image_iff.mpr (core_restrict_injOn Q C U T),
        Finset.sum_image (core_restrict_injOn Q C U T)] at hh
      exact hh
    · have he : F.filter (fun W => W \ U = T) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro W hw
        have ht := (Finset.mem_filter.mp hw).2
        apply hT
        rw [← ht]
        exact Finset.sdiff_disjoint
      simp [he]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => h t)
  have hc : (∑ t : Finset R, (F.filter (fun W => W \ U = t)).card) = F.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter F
      (Finset.univ : Finset (Finset R)) (fun W => W \ U)
  have hs : (∑ t : Finset R, ∑ W ∈ F.filter (fun W => W \ U = t),
      (toRestricted U W).card) = ∑ W ∈ F, (toRestricted U W).card := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro W _
    simp
  simp only [← Finset.sum_mul, ← Finset.mul_sum] at hsum
  rw [hc,hs] at hsum
  have hcard : ∀ W : Finset R, (toRestricted U W).card = (W ∩ U).card := by
    intro W
    have he : fromRestricted (toRestricted U W) = W ∩ U := by
      ext r
      simp [and_comm]
    rw [← he]
    simp [fromRestricted]
  simpa only [Fintype.card_coe,hcard] using hsum


omit [Fintype R] in
theorem local_supplierCore_isRAF (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank)
    (hU : SupplierCore Q C U) : IsRAF Q C U := by
  classical
  have hfg : FoodGenerated Q (U ∪ ∅) := by
    apply internal_rank_foodGenerated Q U rank hrank U ∅ (Finset.Subset.refl U)
    · simp
    · intro r hr x hx hn
      obtain ⟨p,hp,hs⟩ := hU.2 r hr
      exact ⟨p,Finset.mem_union_left _ hp,hs.1 (Finset.mem_sdiff.mpr ⟨hx,hn⟩)⟩
  have hf : FoodGenerated Q U := by simpa using hfg
  apply (isRAF_iff_foodGenerated_and_productGraph Q C U).mpr
  refine ⟨hU.1,hf,?_⟩
  intro r hr
  obtain ⟨p,hp,hs⟩ := hU.2 r hr
  exact (completeSupplier_local Q C hs hp).2

theorem locally_ranked_supplier_abundance (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank)
    (hU : SupplierCore Q C U) :
    IsRAF Q C U ∧
    (∀ T, (extensionFibre Q C U T).card * Fintype.card {r // r ∈ U} ≤
      2 * ∑ S ∈ extensionFibre Q C U T, S.card) ∧
    ((fixedFamily Q C).card * U.card ≤ 2 * ∑ W ∈ fixedFamily Q C, (W ∩ U).card) ∧
    ∃ r ∈ U, (fixedFamily Q C).card ≤ 2 * ((fixedFamily Q C).filter (fun W => r ∈ W)).card :=
  ⟨local_supplierCore_isRAF Q C U rank hrank hU,
   fun T => localSupplierFibre_average Q C U rank hrank T hU,
   local_supplier_core_global_average Q C U rank hrank hU,
   local_supplier_core_exists_abundant Q C U rank hrank hU⟩

end RAF.Frankl
