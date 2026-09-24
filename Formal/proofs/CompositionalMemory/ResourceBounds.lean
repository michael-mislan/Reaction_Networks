import proofs.CompositionalMemory.SourceScaling
import proofs.CompositionalMemory.LogBudgetComparison

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

def residentMolecules {k : ℕ} (s : ModularCountState k) : ℕ := ∑ i, ∑ a, s.1 i a

theorem source_resident_bounds {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (b : ℝ) (hb : b ≤ 1/32000000)
    (s : {s // s ∈ productDomain N (sourceWordCenter σ) (wordEnergy σ) b}) :
    ((k*N : ℕ) : ℝ)/2 ≤ residentMolecules s.val ∧
      residentMolecules s.val ≤ 280*(k*N) := by
  have hz := (word_membrane_rate_bounds hk N hN sourceWordLow sourceWordHigh 1 σ
    (by norm_num) sourceWordLow_spec.1 sourceWordHigh_spec.1 b hb s.val s.property).1
  simp only [one_div,one_mul] at hz
  have hu : residentMolecules s.val ≤ 280*(k*N) := by
    calc
      _ ≤ ∑ _i : Fin k, 280*N := Finset.sum_le_sum (fun i _ => product_domain_module_total N _ _ b s i)
      _ = _ := by simp; ring
  refine ⟨?_,hu⟩
  have hlo : (∑ i, s.val.1 i 2) ≤ residentMolecules s.val :=
    Finset.sum_le_sum (fun i _ => Finset.single_le_sum (fun a _ => Nat.zero_le (s.val.1 i a)) (Finset.mem_univ 2))
  have hlor : (∑ i, (s.val.1 i 2 : ℝ)) ≤ (residentMolecules s.val : ℝ) := by exact_mod_cast hlo
  linarith only [hz,hlor]

end CompositionalMemory
