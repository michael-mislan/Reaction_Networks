import proofs.RAF.Frankl.LocallyRankedSupplierCore
import proofs.RAFQueryCompilation.Pruning

namespace RAF.Frankl.LocalSupplierExample
open RAF RAFQueryCompilation
def source : CRS (Fin 3) (Fin 3) where
  food := {0}
  inputs := ![{0},{1},{2}]
  outputs := ![{1},{2},{1}]
def catalysts (x r : Fin 3) : Prop := if r=0 then x=2 else x=0
instance (x r : Fin 3) : Decidable (catalysts x r) := by unfold catalysts; infer_instance
def core : Finset (Fin 3) := {0,1}
def rank (r : Fin 3) : ℕ := if r=0 then 0 else 1
theorem internal_rank : InternalSubstrateRank source core rank := by
  unfold InternalSubstrateRank
  decide
theorem certified : SupplierCore source catalysts core := by
  unfold SupplierCore CompleteSupplier
  decide
theorem no_global_rank : ¬ ∃ rank : Fin 3 → ℕ, SubstrateRank source rank := by
  rintro ⟨rank,h⟩
  have h12 := h 1 2 2 (by decide) (by decide) (by decide)
  have h21 := h 2 1 1 (by decide) (by decide) (by decide)
  omega
theorem abundant : ∃ r ∈ core, (fixedFamily source catalysts).card ≤
    2*((fixedFamily source catalysts).filter (fun W => r ∈ W)).card :=
  local_supplier_core_exists_abundant source catalysts core rank internal_rank certified

theorem exact_fixed_family : fixedFamily source catalysts = {∅,{0,1},{0,1,2}} := by
  classical
  have hc : ∀ W : Finset (Fin 3), executablePrune source catalysts W = W ↔
      W ∈ ({∅,{0,1},{0,1,2}} : Finset (Finset (Fin 3))) := by decide
  ext W
  rw [mem_fixedFamily]
  by_cases he : W = ∅
  · subst W
    simp
  · rw [isRAF_iff_nonempty_prune_eq]
    simp only [he, false_or, Finset.nonempty_iff_ne_empty]
    rw [← executablePrune_eq]
    exact ⟨fun h => (hc W).mp h.2, fun h => ⟨he, (hc W).mpr h⟩⟩

theorem exterior_not_generated : ¬ FoodGenerated source ({2} : Finset (Fin 3)) := by
  intro h
  obtain ⟨k,hk⟩ := h 2 (by simp)
  have hc : closureAt source ({2} : Finset (Fin 3)) k = source.food :=
    closureAt_eq_food_of_no_seed source {2} (by unfold SeedReaction; decide) k
  have hm := hk (show (2 : Fin 3) ∈ source.inputs 2 by decide)
  rw [hc] at hm
  exact (show (2 : Fin 3) ∉ source.food by decide) hm

end RAF.Frankl.LocalSupplierExample

