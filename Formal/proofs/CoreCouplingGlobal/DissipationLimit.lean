import Mathlib

namespace CoreCouplingGlobal
open Set Filter Topology

/-- A uniformly continuous nonnegative dissipation must vanish if its potential has a limit. -/
theorem dissipation_tendsto_zero (V v q : ℝ → ℝ) (T L : ℝ)
    (hd : ∀ t, T ≤ t → HasDerivAt V (v t) t)
    (hv : ∀ t, T ≤ t → v t ≤ -q t)
    (hq : ∀ t, T ≤ t → 0 ≤ q t)
    (hu : UniformContinuousOn q (Ici T)) (hlim : Tendsto V atTop (𝓝 L)) :
    Tendsto q atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨δ,hδ,hδq⟩ := Metric.uniformContinuousOn_iff.1 hu (ε/2) (by positivity)
  let h := δ/2
  have hh : 0 < h := by dsimp [h]; positivity
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.1 hlim (ε*h/8) (by positivity)
  refine ⟨max T N,?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have htN : N ≤ t := le_trans (le_max_right _ _) ht
  have hqa := hq t htT
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hqa]
  by_contra hbad
  have hlarge : ε ≤ q t := le_of_not_gt hbad
  have hlocal : ∀ s ∈ Icc t (t+h), ε/2 < q s := by
    intro s hs
    have hsT : T ≤ s := le_trans htT hs.1
    have hdist : dist s t < δ := by
      rw [Real.dist_eq,abs_of_nonneg (by linarith [hs.1] : 0 ≤ s-t)]
      dsimp [h] at hs
      linarith [hs.2]
    have hdiff := hδq s (show s ∈ Ici T from hsT) t (show t ∈ Ici T from htT) hdist
    rw [Real.dist_eq] at hdiff
    have hdiff' := (abs_lt.1 hdiff).1
    linarith
  obtain ⟨s,hs,heq⟩ := exists_hasDerivAt_eq_slope V v (show t < t+h by linarith)
    (fun s hs => (hd s (le_trans htT hs.1)).continuousAt.continuousWithinAt)
    (fun s hs => hd s (by linarith [hs.1]))
  have hvs := hv s (by linarith [hs.1])
  have hqs := hlocal s ⟨hs.1.le,hs.2.le⟩
  have hvend := hN (t+h) (by linarith)
  have hvstart := hN t htN
  rw [Real.dist_eq] at hvend hvstart
  have hend := (abs_lt.1 hvend).1
  have hstart := (abs_lt.1 hvstart).2
  have hslope : v s*h = V (t+h)-V t := by
    have hh0 : t+h-t ≠ 0 := by linarith
    have hh' := (eq_div_iff hh0).1 heq
    nlinarith only [hh']
  have hdrop := mul_lt_mul_of_pos_right (show v s < -ε/2 by linarith) hh
  nlinarith only [hslope,hdrop,hend,hstart,hε,hh]

theorem potential_tendsto_of_bounded_dissipation (V v q : ℝ → ℝ) (T M : ℝ)
    (hd : ∀ t, T ≤ t → HasDerivAt V (v t) t)
    (hv : ∀ t, T ≤ t → v t ≤ -q t)
    (hq : ∀ t, T ≤ t → 0 ≤ q t)
    (hM : ∀ t, T ≤ t → M ≤ V t) :
    ∃ L, Tendsto V atTop (𝓝 L) := by
  have hanti : AntitoneOn V (Ici T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici T)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => by have h₁ := hv t (interior_subset ht); have h₂ := hq t (interior_subset ht); linarith)
  let W : ℝ → ℝ := fun t => V (max T t)
  have hW : Antitone W := fun x y hxy =>
    hanti (show max T x ∈ Ici T from le_max_left T x)
      (show max T y ∈ Ici T from le_max_left T y) (max_le_max_left T hxy)
  have hbd : BddBelow (range W) := ⟨M,by rintro _ ⟨t,rfl⟩; exact hM _ (le_max_left _ _)⟩
  refine ⟨⨅ t, W t,?_⟩
  have ht := tendsto_atTop_ciInf hW hbd
  apply ht.congr'
  filter_upwards [eventually_ge_atTop T] with t ht
  dsimp [W]
  rw [max_eq_right ht]

end CoreCouplingGlobal
