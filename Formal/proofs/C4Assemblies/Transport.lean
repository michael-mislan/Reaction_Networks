import Mathlib

namespace C4Assemblies
noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Equal-volume exchange; the diagonal contributes zero. -/
def diffusion (k : ι → ι → ℝ) (z : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, k i j * (z j - z i)

theorem diffusion_const (k : ι → ι → ℝ) (a : ℝ) (i : ι) :
    diffusion k (fun _ => a) i = 0 := by simp [diffusion]

theorem diffusion_add (k : ι → ι → ℝ) (x y : ι → ℝ) (i : ι) :
    diffusion k (fun j => x j + y j) i = diffusion k x i + diffusion k y i := by
  simp only [diffusion, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem diffusion_mul (k : ι → ι → ℝ) (a : ℝ) (x : ι → ℝ) (i : ι) :
    diffusion k (fun j => a * x j) i = a * diffusion k x i := by
  simp only [diffusion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem diffusion_sum_zero (k : ι → ι → ℝ) (hs : ∀ i j, k i j = k j i)
    (z : ι → ℝ) : ∑ i, diffusion k z i = 0 := by
  have swap : (∑ i, ∑ j, k i j * z j) = ∑ i, ∑ j, k i j * z i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  simp only [diffusion, mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr swap

theorem diffusion_at_min (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j)
    (z : ι → ℝ) (i : ι) (hm : ∀ j, z i ≤ z j) : 0 ≤ diffusion k z i := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hk i j) (sub_nonneg.mpr (hm j))

theorem diffusion_at_max (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j)
    (z : ι → ℝ) (i : ι) (hm : ∀ j, z j ≤ z i) : diffusion k z i ≤ 0 := by
  exact Finset.sum_nonpos fun j _ =>
    mul_nonpos_of_nonneg_of_nonpos (hk i j) (sub_nonpos.mpr (hm j))

/-- First-contact drift surplus. No derivative of a nonsmooth minimum is used. -/
theorem strict_growth_at_contact (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j)
    (z v : ι → ℝ) (b : ℝ) (hb : 0 < b) (i : ι)
    (hall : ∀ j, b ≤ z j) (hi : z i = b) (hv : (2/3)*z i ≤ v i) :
    (3/5)*b < v i + diffusion k z i := by
  have hd := diffusion_at_min k hk z i (by intro j; rw [hi]; exact hall j)
  rw [hi] at hv
  linarith

end
end C4Assemblies
