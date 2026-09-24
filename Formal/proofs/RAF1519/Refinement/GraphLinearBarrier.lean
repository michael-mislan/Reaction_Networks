import proofs.RAF1519.Refinement.GraphNoiseBounds

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

theorem graph_linear_upper {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j = k j i)
    (f v : ℝ → ι → ℝ) (T c L : ℝ) (hL : 0 ≤ L)
    (hc : ∀ i, ContinuousOn (fun t => f t i) (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, ∀ i, HasDerivWithinAt (fun u => f u i) (v t i) (Set.Ici t) t)
    (h0 : ∀ i, f 0 i ≤ c)
    (hv : ∀ t ∈ Set.Ico 0 T, ∀ i, v t i ≤ graphDiffusion k (f t) i-f t i+L) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, f t i ≤ c*Real.exp (-t)+L := by
  let B : ℝ → ℝ := fun t => c*Real.exp (-t)+L
  have hB (t : ℝ) : HasDerivAt B (-c*Real.exp (-t)) t := by
    simpa [B] using ((((hasDerivAt_id t).neg).exp).const_mul c).add_const L
  have hvw : ∀ t ∈ Set.Ico 0 T, ∀ i, 0 < f t i-B t →
      v t i+c*Real.exp (-t) ≤ ∑ j, k i j*((f t j-B t)-(f t i-B t)) := by
    intro t ht i hi
    change v t i+c*Real.exp (-t) ≤ graphDiffusion k (fun j => f t j-B t) i
    rw [graphDiffusion_sub_const]
    dsimp [B] at hi
    linarith [hv t ht i]
  have hb := graph_right_barrier k hk hsym
    (fun t i => f t i-B t) (fun t i => v t i+c*Real.exp (-t)) T
    (fun i => (hc i).sub (fun t _ => (hB t).continuousAt.continuousWithinAt))
    (fun t ht i => by simpa only [sub_neg_eq_add,neg_mul] using (hd t ht i).sub (hB t).hasDerivWithinAt)
    (fun i => by dsimp [B]; simp only [neg_zero,Real.exp_zero,mul_one]; linarith [h0 i])
    hvw
  intro t ht i
  have hh := hb t ht i
  dsimp [B] at hh
  linarith

theorem graph_linear_absolute {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j = k j i)
    (f v : ℝ → ι → ℝ) (T c L : ℝ) (hL : 0 ≤ L)
    (hc : ∀ i, ContinuousOn (fun t => f t i) (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, ∀ i, HasDerivWithinAt (fun u => f u i) (v t i) (Set.Ici t) t)
    (h0 : ∀ i, |f 0 i| ≤ c)
    (hv : ∀ t ∈ Set.Ico 0 T, ∀ i, |v t i-(graphDiffusion k (f t) i-f t i)| ≤ L) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, |f t i| ≤ c*Real.exp (-t)+L := by
  have hu := graph_linear_upper k hk hsym f v T c L hL hc hd
    (fun i => (le_abs_self _).trans (h0 i))
    (fun t ht i => by have hh := (abs_le.mp (hv t ht i)).2; linarith)
  have hneg (x : ι → ℝ) (i : ι) : graphDiffusion k (fun j => -x j) i = -graphDiffusion k x i := by
    unfold graphDiffusion
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hl := graph_linear_upper k hk hsym (fun t i => -f t i) (fun t i => -v t i)
    T c L hL (fun i => (hc i).neg) (fun t ht i => (hd t ht i).neg)
    (fun i => (neg_le_abs _).trans (h0 i))
    (fun t ht i => by rw [hneg]; have hh := (abs_le.mp (hv t ht i)).1; linarith)
  intro t ht i
  exact abs_le.mpr ⟨by linarith [hl t ht i],hu t ht i⟩

end
end RAF1519.Refinement

