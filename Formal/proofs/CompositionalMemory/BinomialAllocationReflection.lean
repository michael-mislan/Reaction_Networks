import proofs.CompositionalMemory.BinomialAllocationMeasure
import Mathlib.Data.Fin.Rev

namespace CompositionalMemory
open MeasureTheory HeritableCompositions

theorem fair_binomial_reflection (n k : ℕ) (hk : k ≤ n) :
    fairBinomialWeight n (n-k)=fairBinomialWeight n k := by
  unfold fairBinomialWeight
  rw [Nat.choose_symm hk]

theorem fair_allocation_reflection (n : ℕ) :
    MeasurePreserving (fun k : ℕ => n-k) (fairAllocationMeasure n) (fairAllocationMeasure n) := by
  refine ⟨measurable_of_countable _,?_⟩
  unfold fairAllocationMeasure
  rw [Measure.map_sum (measurable_of_countable _).aemeasurable]
  simp_rw [Measure.map_smul,Measure.map_dirac]
  have hh : (fun k : Fin (n+1) =>
      ENNReal.ofReal (fairBinomialWeight n k.val) • Measure.dirac (n-k.val))=
      (fun k : Fin (n+1) => ENNReal.ofReal (fairBinomialWeight n k.val) • Measure.dirac k.val) ∘ Fin.revPerm := by
    funext k
    have hr : ((Fin.revPerm k : Fin (n+1)).val)=n-k.val := by
      simp only [Fin.revPerm_apply,Fin.val_rev]
      omega
    simp only [Function.comp_apply,hr,fair_binomial_reflection n k.val (Nat.le_of_lt_succ k.isLt)]
  rw [hh,Measure.sum_comp_equiv]

end CompositionalMemory
