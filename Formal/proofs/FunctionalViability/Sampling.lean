import proofs.FunctionalViability.RecoverySource

namespace FunctionalViability
noncomputable section
open scoped BigOperators

/-- Explicit independent history weights, with no likelihood postulate. -/
def historyMass {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (n : ℕ) : ℝ :=
  ∑ h : Fin n → Ω, ∏ i, P (h i)

/-- Mass of the all-negative event, obtained by zeroing each excluded path. -/
def allNegative {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (neg : Ω → Bool) (n : ℕ) : ℝ :=
  ∑ h : Fin n → Ω, ∏ i, if neg (h i) then P (h i) else 0

theorem history_normalized {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    (hP : ∑ i, P i = 1) (n : ℕ) : historyMass P n = 1 := by
  rw [historyMass, ← Fintype.sum_pow, hP, one_pow]

theorem negative_factorization {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (neg : Ω → Bool) (n : ℕ) :
    allNegative P neg n = (∑ i, if neg i then P i else 0)^n := by
  exact (Fintype.sum_pow (fun i => if neg i then P i else 0) n).symm

variable {K : Type*} [Fintype K]

def mixturePath (μ x y : K → ℝ) (p w : ℝ) (a : K × Fin 7) : ℝ :=
  μ a.1 * pathWeight p w (x a.1) (y a.1) a.2

def meanResponse (μ x y : K → ℝ) (w : ℝ) : ℝ :=
  ∑ k, μ k * response w (x k) (y k)

theorem mixture_normalized (μ x y : K → ℝ) (p w : ℝ)
    (hμ : ∑ k, μ k = 1) : ∑ a, mixturePath μ x y p w a = 1 := by
  simp only [mixturePath, Fintype.sum_prod_type, ← Finset.mul_sum, source_normalized,
    mul_one]
  exact hμ

omit [Fintype K] in
theorem mixture_nonneg (μ x y : K → ℝ) (p w : ℝ)
    (hμ : ∀ k, 0 ≤ μ k) (hp : 0 ≤ p ∧ p ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1)
    (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1) (hy : ∀ k, 0 ≤ y k ∧ y k ≤ 1) :
    ∀ a, 0 ≤ mixturePath μ x y p w a := by
  intro a
  exact mul_nonneg (hμ a.1) (source_nonneg _ _ _ _ hp hw (hx a.1) (hy a.1) a.2)

theorem mixture_negative (μ x y : K → ℝ) (p w : ℝ)
    (hμ : ∑ k, μ k = 1) :
    (∑ a, if negative a.2 then mixturePath μ x y p w a else 0) =
      1-p*meanResponse μ x y w := by
  simp only [Fintype.sum_prod_type, mixturePath]
  have hi (k : K) :
      (∑ j, if negative j then μ k * pathWeight p w (x k) (y k) j else 0) =
        μ k * (1-p*response w (x k) (y k)) := by
    rw [← source_negative]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp_all
  simp_rw [hi]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, meanResponse]
  rw [hμ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem mean_floor (μ x y : K → ℝ) (d : ℝ)
    (hμ : ∀ k, 0 ≤ μ k) (hs : ∑ k, μ k = 1)
    (ha : ∀ k, |x k-y k| ≤ d) : floor d ≤ meanResponse μ x y (1/2) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    mul_le_mul_of_nonneg_left (alignment_floor (x k) (y k) d (ha k)) (hμ k))
  simpa [meanResponse, ← Finset.sum_mul, hs] using h

theorem mean_le_one (μ x y : K → ℝ) (w : ℝ)
    (hμ : ∀ k, 0 ≤ μ k) (hs : ∑ k, μ k = 1)
    (hw : 0 ≤ w ∧ w ≤ 1)
    (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1) (hy : ∀ k, 0 ≤ y k ∧ y k ≤ 1) :
    meanResponse μ x y w ≤ 1 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    mul_le_mul_of_nonneg_left (response_le_one w (x k) (y k) hw (hx k) (hy k)) (hμ k))
  simpa [meanResponse, hs] using h

theorem source_sampling_identity (μ x y : K → ℝ) (p w : ℝ)
    (hs : ∑ k, μ k = 1) (n : ℕ) :
    allNegative (mixturePath μ x y p w) (fun a => negative a.2) n =
      (1-p*meanResponse μ x y w)^n := by
  rw [negative_factorization, mixture_negative μ x y p w hs]

end
end FunctionalViability
