import proofs.OptimalAffinityRealizability.ExponentialTangentGap
import Mathlib

namespace OptimalAffinityRealizability

open scoped BigOperators
noncomputable section

def normalizedResponseCurrent {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) (q x : ι → ℝ) (i : ι) : ℝ :=
  (q i * Real.exp (x i) - Real.exp (T.transpose.mulVec x i)) / (q i - 1)

theorem responseMinimum_comparison {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) (f q x : ι → ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hf : ∀ i, 0 < f i)
    (hr : ∀ i, T.transpose.mulVec f i = q i * f i)
    (k : ι) (hk : ∀ i, x k / f k ≤ x i / f i) :
    q k * x k ≤ T.transpose.mulVec x k := by
  have hs : ∀ i, (x k / f k) * f i ≤ x i := fun i =>
    (le_div_iff₀ (hf i)).mp (hk i)
  calc
    q k * x k = (x k / f k) * (q k * f k) := by
      field_simp [ne_of_gt (hf k)]
    _ = (x k / f k) * T.transpose.mulVec f k := by rw [hr]
    _ = ∑ i, T i k * ((x k / f k) * f i) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, T i k * x i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hs i) (hT i k)
    _ = T.transpose.mulVec x k := rfl

theorem responseMinimum_current_le_one {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) (f q x : ι → ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hf : ∀ i, 0 < f i)
    (hq : ∀ i, 1 < q i)
    (hr : ∀ i, T.transpose.mulVec f i = q i * f i)
    (k : ι) (hk : ∀ i, x k / f k ≤ x i / f i) :
    normalizedResponseCurrent T q x k ≤ 1 := by
  have hc := Real.exp_le_exp.mpr (responseMinimum_comparison T f q x hT hf hr k hk)
  have hs := exp_tangent_gap_nonneg (a := x k) (hq k)
  unfold normalizedResponseCurrent
  apply (div_le_one (sub_pos.mpr (hq k))).mpr
  linarith

theorem commonResponseCurrent_le_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : Matrix ι ι ℝ) (f q x : ι → ℝ) (t : ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hf : ∀ i, 0 < f i)
    (hq : ∀ i, 1 < q i)
    (hr : ∀ i, T.transpose.mulVec f i = q i * f i)
    (ht : ∀ i, normalizedResponseCurrent T q x i = t) : t ≤ 1 := by
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ
    (fun i => x i / f i) Finset.univ_nonempty
  rw [← ht k]
  exact responseMinimum_current_le_one T f q x hT hf hq hr k
    (fun i => hk i (Finset.mem_univ i))

end
end OptimalAffinityRealizability
