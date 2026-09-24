import proofs.RAF1519.Refinement.GraphLinearBarrier

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

theorem graphDiffusion_sub {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (x y : ι → ℝ) (i : ι) :
    graphDiffusion k (fun j => x j-y j) i = graphDiffusion k x i-graphDiffusion k y i := by
  unfold graphDiffusion
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The material comparison is applied to the continuous compensated primitive,
    while X may be a jump path. Noise is needed only before the final endpoint. -/
theorem compensated_material_primitive_bound {ι : Type*} [Fintype ι]
    (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j = k j i)
    (Δ η : ℝ) (hΔ : 0 ≤ Δ) (hη : 0 ≤ η) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (X F v : ℝ → ι → ℝ) (T c : ℝ)
    (hc : ∀ i, ContinuousOn (fun t => F t i) (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, ∀ i, HasDerivWithinAt (fun u => F u i) (v t i) (Set.Ici t) t)
    (h0 : ∀ i, |F 0 i-1| ≤ c)
    (hv : ∀ t ∈ Set.Ico 0 T, ∀ i, v t i = 1-X t i+graphDiffusion k (X t) i)
    (hnoise : ∀ t ∈ Set.Ico 0 T, ∀ i, |X t i-F t i| ≤ η) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, |F t i-1| ≤ c*Real.exp (-t)+(2*Δ+1)*η := by
  apply graph_linear_absolute k hk hsym (fun t i => F t i-1) v T c ((2*Δ+1)*η) (by positivity)
    (fun i => (hc i).sub continuousOn_const) (fun t ht i => (hd t ht i).sub_const 1) h0
  intro t ht i
  have hb := graph_killing_noise_bound k hk Δ η 1 hη (by norm_num) hdegree
    (fun j => X t j-F t j) (hnoise t ht) i
  change |v t i-(graphDiffusion k (fun j => F t j-1) i-(F t i-1))| ≤ _
  rw [graphDiffusion_sub_const,hv t ht i]
  have he : 1-X t i+graphDiffusion k (X t) i-(graphDiffusion k (F t) i-(F t i-1)) =
      graphDiffusion k (fun j => X t j-F t j) i-1*(X t i-F t i) := by
    rw [graphDiffusion_sub]
    ring
  rw [he]
  exact hb

theorem material_observed_from_primitive (X F c L η t : ℝ)
    (hF : |F-1| ≤ c*Real.exp (-t)+L) (hnoise : |X-F| ≤ η) :
    |X-1| ≤ c*Real.exp (-t)+L+η := by
  have he : X-1 = (X-F)+(F-1) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

end
end RAF1519.Refinement
