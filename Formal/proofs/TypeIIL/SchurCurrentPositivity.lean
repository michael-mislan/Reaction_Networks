import Mathlib

namespace TypeIIL

open scoped BigOperators

/-- Abstract sign bridge for the weighted source Schur complement.  If
`E D = Mfi`, the full fork residual and every internal residual are strictly
positive, and `E` is entrywise nonpositive, then the reduced fork residual is
strictly positive.  This avoids assuming a sign for the mixed boundary block
`Mfi`, which is false in source-faithful weighted examples.  Internal
residuals need only be nonnegative; unit nonfork ordered-secant rows attain
equality. -/
theorem schur_reduced_base_current_pos
    {F I : Type*} [Fintype F] [Fintype I]
    (Mff : Matrix F F ℝ) (Mfi : Matrix F I ℝ)
    (Mif : Matrix I F ℝ) (D : Matrix I I ℝ) (E : Matrix F I ℝ)
    (Jf : F → ℝ) (Ji : I → ℝ)
    (hE : ∀ f i, E f i ≤ 0)
    (hfactor : ∀ f i, ∑ k, E f k * D k i = Mfi f i)
    (hfork : ∀ f, 0 <
      (∑ g, Mff f g * Jf g) + ∑ i, Mfi f i * Ji i)
    (hinternal : ∀ i, 0 ≤
      (∑ g, Mif i g * Jf g) + ∑ k, D i k * Ji k) :
    ∀ f, 0 <
      (∑ g, Mff f g * Jf g) -
        ∑ i, E f i * (∑ g, Mif i g * Jf g) := by
  classical
  intro f
  have hcorrection :
      ∑ i, E f i * (∑ g, Mif i g * Jf g) ≤
        -(∑ i, Mfi f i * Ji i) := by
    have hterm : ∀ i,
        E f i * (∑ g, Mif i g * Jf g) ≤
          E f i * (-(∑ k, D i k * Ji k)) := by
      intro i
      apply mul_le_mul_of_nonpos_left _ (hE f i)
      linarith [hinternal i]
    calc
      ∑ i, E f i * (∑ g, Mif i g * Jf g) ≤
          ∑ i, E f i * (-(∑ k, D i k * Ji k)) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = -(∑ i, Mfi f i * Ji i) := by
        simp_rw [mul_neg, Finset.sum_neg_distrib]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [← hfactor f i, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
  linarith [hfork f]

/-- Positive-current normalization of a cyclic three-term row. -/
theorem cyclic_row_normalized_gain
    {A B C Jprev J Jnext : ℝ}
    (hB : 0 < B) (hJ : 0 < J)
    (hrow : 0 < B * J - A * Jprev + C * Jnext) :
    A * Jprev / (B * J) < 1 + C * Jnext / (B * J) := by
  have hden : 0 < B * J := mul_pos hB hJ
  apply (div_lt_iff₀ hden).2
  field_simp [ne_of_gt hden]
  nlinarith

end TypeIIL
