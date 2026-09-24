import Mathlib

namespace TypeIIL

open Finset

/-- A positive quantity cannot grow strictly around a finite permutation
cycle when every multiplicative gain is at least one.  This is the final
telescoping contradiction in the strict Type II_l argument. -/
theorem impossible_cyclic_growth
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (next : ι ≃ ι) (m d delta : ι → ℝ)
    (hm : ∀ i, 1 ≤ m i) (hd : ∀ i, 0 < d i)
    (hdelta : ∀ i, delta i ≠ 0)
    (hgrow : ∀ i,
      m i * (d i * |delta i|) < d (next i) * |delta (next i)|) : False := by
  let base : ι → ℝ := fun i => d i * |delta i|
  let gained : ι → ℝ := fun i => m i * base i
  have hbase : ∀ i, 0 < base i := by
    intro i
    exact mul_pos (hd i) (abs_pos.mpr (hdelta i))
  have hle : ∀ i, base i ≤ gained i := by
    intro i
    dsimp [gained]
    nlinarith [hbase i, hm i]
  have hprod_le : ∏ i, base i ≤ ∏ i, gained i := by
    apply Finset.prod_le_prod
    · intro i hi
      exact le_of_lt (hbase i)
    · intro i hi
      exact hle i
  have hprod_lt : ∏ i, gained i < ∏ i, base (next i) := by
    apply Finset.prod_lt_prod
    · intro i hi
      dsimp [gained]
      exact mul_pos (lt_of_lt_of_le zero_lt_one (hm i)) (hbase i)
    · intro i hi
      exact le_of_lt (hgrow i)
    · let i : ι := Classical.choice (inferInstance : Nonempty ι)
      exact ⟨i, Finset.mem_univ i, hgrow i⟩
  have hperm : (∏ i, base (next i)) = ∏ i, base i :=
    Equiv.prod_comp next base
  rw [hperm] at hprod_lt
  exact (not_lt_of_ge hprod_le) hprod_lt

end TypeIIL
