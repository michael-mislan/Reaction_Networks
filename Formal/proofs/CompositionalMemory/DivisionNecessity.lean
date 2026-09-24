import proofs.CompositionalMemory.PartitionNecessity

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

theorem product_domain_module_total {k : ℕ} (N : ℕ) (center : Fin k → Point)
    (E : Fin k → Point → ℝ) (b : ℝ)
    (s : {s // s ∈ productDomain N center E b}) (i : Fin k) :
    ∑ a, s.val.1 i a ≤ 280*N := by
  classical
  have hm := (Finset.mem_product.mp (Finset.mem_filter.mp s.property).1).1
  have hc := (mem_modularCountBox (2*N) s.val.1).mp hm i
  calc
    _ ≤ ∑ _a : Fin 4, 35*(2*N) := Finset.sum_le_sum (fun a _ => hc a)
    _ = _ := by simp; omega

theorem source_division_partition_obstruction {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (b : ℝ)
    (s : {s // s ∈ productDomain N (sourceWordCenter σ) (wordEnergy σ) b}) :
    1-(1-(1/2 : ℝ)^(280*N))^k ≤
      (wordPartitionLaw N hN (sourceWordCenter σ) (sourceWordCenter_upper σ) σ s.val.1).mass none :=
  source_partition_failure_lower N hN σ s.val.1 (280*N)
    (product_domain_module_total N _ _ b s)

end CompositionalMemory
