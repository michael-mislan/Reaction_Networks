import proofs.G6PDReserve.DriftComparison
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace G6PDReserve
noncomputable section
open Set

/-- Literal physical-pH field extracted from Nishino Model S1 (k=1).
The biological meaning of an operating floor is a separate input. -/
def storageAging (a b c z : ℝ) : ℝ := -Real.sqrt (b^2-4*a*(c-z))

theorem storage_aging_antitone (z : ℝ → ℝ) (a b c T : ℝ) 
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt z (storageAging a b c (z t)) t) :
    AntitoneOn z (Icc 0 T) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
  · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact neg_nonpos.mpr (Real.sqrt_nonneg _)

/-- Any endpoint still above a declared floor strictly above the radicand-zero
boundary has a finite time budget. No reset or supplied drift inequality. -/
theorem storage_aging_budget (z : ℝ → ℝ) (a b c L T : ℝ)
    (ha : 0 < a) (hT : 0 ≤ T) (hL : 0 < b^2-4*a*(c-L))
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt z (storageAging a b c (z t)) t)
    (hend : L ≤ z T) : T ≤ (z 0-L)/Real.sqrt (b^2-4*a*(c-L)) := by
  let m := Real.sqrt (b^2-4*a*(c-L))
  have hm : 0 < m := Real.sqrt_pos.2 hL
  have hmono := storage_aging_antitone z a b c T hd
  have hfloor (t : ℝ) (ht : t ∈ Icc 0 T) : L ≤ z t :=
    le_trans hend (hmono ht ⟨hT,le_rfl⟩ ht.2)
  have hf : AntitoneOn (fun t => z t+m*t) (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · intro t ht
      exact ((hd t ht).add ((hasDerivAt_id t).const_mul m)).continuousAt.continuousWithinAt
    · intro t ht
      exact ((hd t (interior_subset ht)).add ((hasDerivAt_id t).const_mul m)).differentiableAt.differentiableWithinAt
    · intro t ht
      have hh : HasDerivAt (fun t => z t+m*t) (storageAging a b c (z t)+m) t := by
        simpa using (hd t (interior_subset ht)).add ((hasDerivAt_id t).const_mul m)
      rw [hh.deriv]
      have hz := hfloor t (interior_subset ht)
      have hs : m ≤ Real.sqrt (b^2-4*a*(c-z t)) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      unfold storageAging
      linarith
  have hh := hf (show 0 ∈ Icc (0:ℝ) T from ⟨le_rfl,hT⟩)
    (show T ∈ Icc (0:ℝ) T from ⟨hT,le_rfl⟩) hT
  simp only [mul_zero,add_zero] at hh
  apply (le_div_iff₀ hm).2
  nlinarith

/-- Returning the entire state to its initial value is impossible at positive
time while the original physical-pH state starts above the branch minimum. -/
theorem storage_aging_no_exact_return (z : ℝ → ℝ) (a b c T : ℝ)
    (ha : 0 < a) (hT : 0 < T) (h0 : 0 < b^2-4*a*(c-z 0))
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt z (storageAging a b c (z t)) t) :
    z T ≠ z 0 := by
  intro he
  have hh := storage_aging_budget z a b c (z 0) T ha hT.le h0 hd he.ge
  simp only [sub_self,zero_div] at hh
  linarith

end
end G6PDReserve
