import proofs.OptimalAffinityRealizability.RoutingMatrix
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

namespace OptimalAffinityRealizability

open Matrix
open scoped BigOperators
noncomputable section

def FixedSpaceOne {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ v, P.mulVec v = v → ∃ c : ℝ, v = fun _ => c

theorem pow_mulVec_fixed {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : P.mulVec v = v) (k : ℕ) :
    (P ^ k).mulVec v = v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]

theorem irreducible_nonnegative_fixed_strictlyPositive_of_nonzero {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hirr : P.IsIrreducible)
    {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hfixed : P.mulVec w = w) (hne : w ≠ 0) :
    ∀ i, 0 < w i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < w j := by
    by_contra h
    push Not at h
    apply hne
    funext i
    exact le_antisymm (h i) (hw i)
  intro i
  obtain ⟨k, _, hik⟩ :=
    (Matrix.isIrreducible_iff_exists_pow_pos hP).mp hirr i j
  have hpowNonneg : ∀ a b, 0 ≤ (P ^ k) a b :=
    Matrix.pow_apply_nonneg hP k
  have hpositive : 0 < (P ^ k).mulVec w i := by
    change 0 < ∑ a, (P ^ k) i a * w a
    apply Finset.sum_pos'
    · intro a _
      exact mul_nonneg (hpowNonneg i a) (hw a)
    · exact ⟨j, Finset.mem_univ j, mul_pos hik hj⟩
  rw [pow_mulVec_fixed P w hfixed k] at hpositive
  exact hpositive

/-- Finite irreducible row-stochastic matrices have only constant fixed vectors. -/
theorem irreducible_rowStochastic_fixedSpaceOne {n : ℕ} [Nonempty (Fin n)]
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hirr : P.IsIrreducible)
    (hrow : RowStochastic P) : FixedSpaceOne P := by
  intro v hfixed
  obtain ⟨imax, _, hmax⟩ :=
    Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  let w : Fin n → ℝ := fun j => v imax - v j
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    exact sub_nonneg.mpr (hmax j (Finset.mem_univ j))
  have hwfixed : P.mulVec w = w := by
    funext i
    change (∑ j, P i j * (v imax - v j)) = v imax - v i
    calc
      (∑ j, P i j * (v imax - v j)) =
          (∑ j, P i j) * v imax - ∑ j, P i j * v j := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = v imax - v i := by
        rw [hrow i]
        change 1 * v imax - P.mulVec v i = v imax - v i
        rw [hfixed]
        ring
  have hwzero : w = 0 := by
    by_contra hne
    have hpos := irreducible_nonnegative_fixed_strictlyPositive_of_nonzero
      P hP hirr hw hwfixed hne imax
    change 0 < v imax - v imax at hpos
    linarith
  refine ⟨v imax, ?_⟩
  funext j
  have hz := congrFun hwzero j
  simp [w] at hz
  linarith

def ResponseKernelOne {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (q f : Fin n → ℝ) : Prop :=
  ∀ v, (responseLaplacian T q).mulVec v = 0 ↔
    ∃ c : ℝ, v = c • f

theorem fixedSpaceOne_implies_responseKernelOne {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (q f h : Fin n → ℝ)
    (hresponse : T.transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hf : ∀ i, 0 < f i) (hq : ∀ i, 0 < q i)
    (hfixedSpace : FixedSpaceOne (routingMatrix T q f)) :
    ResponseKernelOne T q f := by
  intro v
  constructor
  · intro hv
    have htriple :
        (Matrix.diagonal (fun i => q i * f i) *
          (1 - routingMatrix T q f) *
            Matrix.diagonal (fun i => (f i)⁻¹)).mulVec v = 0 := by
      rw [← responseLaplacian_routing_factorization T q f hf hq]
      exact hv
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec] at htriple
    have hproduct :
        ((1 - routingMatrix T q f) *
          Matrix.diagonal (fun i => (f i)⁻¹)).mulVec v = 0 := by
      funext i
      have hi := congrFun htriple i
      simp only [Matrix.mulVec_diagonal] at hi
      exact (mul_eq_zero.mp hi).resolve_left
        (mul_ne_zero (ne_of_gt (hq i)) (ne_of_gt (hf i)))
    have hmiddle :
        (1 - routingMatrix T q f).mulVec
          ((Matrix.diagonal (fun i => (f i)⁻¹)).mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec]
      exact hproduct
    have hzfixed :
        (routingMatrix T q f).mulVec
            ((Matrix.diagonal (fun i => (f i)⁻¹)).mulVec v) =
          (Matrix.diagonal (fun i => (f i)⁻¹)).mulVec v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hmiddle
      exact (sub_eq_zero.mp hmiddle).symm
    obtain ⟨c, hc⟩ := hfixedSpace _ hzfixed
    refine ⟨c, ?_⟩
    funext i
    have hi := congrFun hc i
    simp only [Matrix.mulVec_diagonal] at hi
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt (hf i)] at hi ⊢
    linarith
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, responseLaplacian_mul_profile_eq_zero T q f h
      hresponse hratio]
    exact smul_zero c

/-- Irreducible routing is a checkable sufficient condition for response corank one. -/
theorem irreducible_routing_responseKernelOne {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℝ) (q f h : Fin n → ℝ)
    (hresponse : T.transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hf : ∀ i, 0 < f i) (hq : ∀ i, 0 < q i)
    (hP : ∀ i j, 0 ≤ routingMatrix T q f i j)
    (hirr : (routingMatrix T q f).IsIrreducible) :
    ResponseKernelOne T q f := by
  apply fixedSpaceOne_implies_responseKernelOne T q f h hresponse hratio hf hq
  exact irreducible_rowStochastic_fixedSpaceOne
    (routingMatrix T q f) hP hirr
      (routingMatrix_rowStochastic T q f h hresponse hratio hf hq)

end
end OptimalAffinityRealizability
