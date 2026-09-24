import proofs.RAF.Frankl.RankedFoodGeneration
import proofs.RAF.Frankl.CommonSupplierConditioning
import proofs.RAF.Frankl.CoreAbundance

namespace RAF.Frankl
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

def SupplierCore (Q : CRS M R) (C : Catalysis M R) (U : Finset R) : Prop :=
  U.Nonempty ∧ ∀ r ∈ U, ∃ p ∈ U, CompleteSupplier Q C p r

theorem supplierCore_isRAF (Q : CRS M R) (C : Catalysis M R)
    (rank : R → ℕ) (hrank : SubstrateRank Q rank)
    (U : Finset R) (hU : SupplierCore Q C U) : IsRAF Q C U := by
  have hf : U ∈ fixedFamily Q C := by
    rw [ranked_fixed_iff Q C rank hrank]
    intro r hr
    obtain ⟨p,hp,hs⟩ := hU.2 r hr
    exact completeSupplier_local Q C hs hp
  rcases (mem_fixedFamily Q C U).mp hf with he | h
  · exact (hU.1.ne_empty he).elim
  · exact h

def supplierExterior (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (S : Finset {r // r ∈ U}) : Prop :=
  ∀ r ∈ T, LocalSupply Q C (fromRestricted S ∪ T) r

theorem supplier_fibre_iff (Q : CRS M R) (C : Catalysis M R)
    (rank : R → ℕ) (hrank : SubstrateRank Q rank)
    (U T : Finset R) (S : Finset {r // r ∈ U}) :
    fromRestricted S ∪ T ∈ fixedFamily Q C ↔
      supplierExterior Q C U T S ∧
        ∀ r ∈ S, LocalSupply Q C (fromRestricted S ∪ T) r.1 := by
  rw [ranked_fixed_iff Q C rank hrank]
  constructor
  · intro h
    exact ⟨fun r hr => h r (Finset.mem_union_right _ hr),
      fun r hr => h r.1 (Finset.mem_union_left _
        ((mem_fromRestricted S r.1).mpr ⟨r.2,hr⟩))⟩
  · rintro ⟨ht,hs⟩ r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨hu,hr⟩ := (mem_fromRestricted S r).mp hr
      exact hs ⟨r,hu⟩ hr
    · exact ht r hr

theorem supplierFibre_average (Q : CRS M R) (C : Catalysis M R)
    (rank : R → ℕ) (hrank : SubstrateRank Q rank)
    (U T : Finset R) (hU : SupplierCore Q C U) :
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
    (supplierExterior Q C U T)
    (fun hab ha r hr => localSupply_mono Q C (hm hab) (ha r hr))
  have heq : extensionFibre Q C U T = Finset.univ.powerset.filter
      (fun S => supplierExterior Q C U T S ∧ ∀ r ∈ S, L r S) := by
    ext S
    simp only [extensionFibre,Finset.mem_filter,supplier_fibre_iff Q C rank hrank,L]
  rw [heq]
  exact h

/-- Literal source theorem: a ranked ordinary CRS with a complete-supplier core
has an empty-inclusive globally abundant reaction in that core. -/
theorem supplier_core_exists_abundant (Q : CRS M R) (C : Catalysis M R)
    (rank : R → ℕ) (hrank : SubstrateRank Q rank)
    (U : Finset R) (hU : SupplierCore Q C U) :
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
    · have h := supplierFibre_average Q C rank hrank U T hU
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

end RAF.Frankl
