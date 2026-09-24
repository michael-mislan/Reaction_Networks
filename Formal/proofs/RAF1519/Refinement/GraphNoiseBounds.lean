import proofs.RAF1519.Refinement.GraphComparison

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

def graphDiffusion {ι : Type*} [Fintype ι] (k : ι → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, k i j*(x j-x i)

theorem graphDiffusion_sub_const {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (x : ι → ℝ) (c : ℝ) (i : ι) :
    graphDiffusion k (fun j => x j-c) i = graphDiffusion k x i := by
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem graphDiffusion_add {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (x y : ι → ℝ) (i : ι) :
    graphDiffusion k (fun j => x j+y j) i = graphDiffusion k x i+graphDiffusion k y i := by
  unfold graphDiffusion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem graphDiffusion_noise_bound {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (Δ ε : ℝ) (hε : 0 ≤ ε)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (m : ι → ℝ) (hm : ∀ i, |m i| ≤ ε) (i : ι) :
    |graphDiffusion k m i| ≤ 2*Δ*ε := by
  calc
    _ ≤ ∑ j, |k i j*(m j-m i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, k i j*(2*ε) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_of_nonneg (hk i j)]
      apply mul_le_mul_of_nonneg_left _ (hk i j)
      exact (abs_sub (m j) (m i)).trans (by linarith [hm j,hm i])
    _ = (∑ j, k i j)*(2*ε) := by rw [Finset.sum_mul]
    _ ≤ Δ*(2*ε) := mul_le_mul_of_nonneg_right (hdegree i) (by positivity)
    _ = _ := by ring

theorem graph_killing_noise_bound {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (Δ ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (m : ι → ℝ) (hm : ∀ i, |m i| ≤ ε) (i : ι) :
    |graphDiffusion k m i-κ*m i| ≤ (2*Δ+κ)*ε := by
  calc
    _ ≤ |graphDiffusion k m i|+|κ*m i| := abs_sub _ _
    _ ≤ 2*Δ*ε+κ*ε := by
      apply add_le_add (graphDiffusion_noise_bound k hk Δ ε hε hdegree m hm i)
      rw [abs_mul,abs_of_nonneg hκ]
      exact mul_le_mul_of_nonneg_left (hm i) hκ
    _ = _ := by ring

end
end RAF1519.Refinement
