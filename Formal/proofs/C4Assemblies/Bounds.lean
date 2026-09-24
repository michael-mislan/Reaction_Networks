import proofs.C4Assemblies.Comparison

namespace C4Assemblies
noncomputable section
open Set
variable {ι : Type*} [Fintype ι]

/-- A common ceiling needs a drift sign only at a maximizing coordinate. -/
theorem finite_upper_barrier (y v : ℝ → ι → ℝ) (M T : ℝ) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, ∀ i, HasDerivAt (fun s => y s i) (v t i) t)
    (h0 : ∀ i, y 0 i ≤ M)
    (hv : ∀ t ∈ Ico 0 T, ∀ i, M ≤ y t i → (∀ j, y t j ≤ y t i) → v t i ≤ 0) :
    ∀ i, y T i ≤ M := by
  intro i
  by_contra hn
  have hlarge : M < y T i := lt_of_not_ge hn
  let e := (y T i-M)/(2*(T+1))
  have he : 0 < e := by dsimp [e]; positivity
  have hf := finite_strict_lower_barrier
    (fun t j => M+e*(t+1)-y t j) (fun t j => e-v t j) 0 T
    (fun t ht j => by
      convert ((((hasDerivAt_id t).add_const 1).const_mul e).const_add M).sub (hd t ht j) using 1
      ring)
    (fun j => by have hh := h0 j; dsimp; linarith)
    (fun t ht hall j hz => by
      have hM : M ≤ y t j := by dsimp at hz; nlinarith [ht.1]
      have hmax : ∀ l, y t l ≤ y t j := by intro l; have hh := hall l; dsimp at hh hz; linarith
      have hh := hv t ht j hM hmax
      dsimp
      linarith)
    T ⟨hT,le_rfl⟩ i
  have heq : e*(T+1) = (y T i-M)/2 := by
    dsimp [e]
    field_simp
  linarith

theorem finite_lower_barrier (y v : ℝ → ι → ℝ) (M T : ℝ) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, ∀ i, HasDerivAt (fun s => y s i) (v t i) t)
    (h0 : ∀ i, M ≤ y 0 i)
    (hv : ∀ t ∈ Ico 0 T, ∀ i, y t i ≤ M → (∀ j, y t i ≤ y t j) → 0 ≤ v t i) :
    ∀ i, M ≤ y T i := by
  have hh := finite_upper_barrier (fun t i => -y t i) (fun t i => -v t i) (-M) T hT
    (fun t ht i => (hd t ht i).neg) (fun i => by have := h0 i; linarith)
    (fun t ht i hi hall => by
      have h := hv t ht i (by linarith) (fun j => by have := hall j; linarith)
      linarith)
  intro i
  have := hh i
  linarith

theorem diffusion_lower_bound (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j)
    (y v : ℝ → ι → ℝ) (M T : ℝ) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, ∀ i, HasDerivAt (fun s => y s i) (v t i) t)
    (h0 : ∀ i, M ≤ y 0 i)
    (hv : ∀ t ∈ Ico 0 T, ∀ i, diffusion k (y t) i ≤ v t i) :
    ∀ i, M ≤ y T i := by
  apply finite_lower_barrier y v M T hT hd h0
  intro t ht i _ hm
  exact (diffusion_at_min k hk (y t) i hm).trans (hv t ht i)

end
end C4Assemblies
