import proofs.CoreCouplingGlobal.DissipationLimit

namespace CoreCouplingGlobal
open Set Filter Topology

/-- Compactness supplies the bounded potential and uniform continuity required by dissipation. -/
theorem compact_trajectory_dissipation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hK : IsCompact K) (f : E → E) (P q : E → ℝ)
    (hf : ContinuousOn f K) (hP : ContinuousOn P K) (hq : ContinuousOn q K)
    (hq0 : ∀ x ∈ K, 0 ≤ q x) (X : ℝ → E) (T : ℝ)
    (hXK : ∀ t, T ≤ t → X t ∈ K)
    (hdX : ∀ t, T ≤ t → HasDerivAt X (f (X t)) t)
    (henergy : ∀ t, T ≤ t → ∃ v, HasDerivAt (fun s => P (X s)) v t ∧ v ≤ -q (X t)) :
    Tendsto (fun t => q (X t)) atTop (𝓝 0) := by
  obtain ⟨M,hM⟩ := hK.bddBelow_image hP
  obtain ⟨C,hC⟩ := hK.bddAbove_image hf.nnnorm
  have hlip : LipschitzOnWith C X (Ici T) :=
    (convex_Ici T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hdX t ht).hasDerivWithinAt)
      (fun t ht => hC (mem_image_of_mem _ (hXK t ht)))
  have hu : UniformContinuousOn (fun t => q (X t)) (Ici T) :=
    (hK.uniformContinuousOn_of_continuous hq).comp hlip.uniformContinuousOn hXK
  classical
  let v : ℝ → ℝ := fun t => if ht : T ≤ t then (henergy t ht).choose else 0
  have hdv : ∀ t, T ≤ t → HasDerivAt (fun s => P (X s)) (v t) t := by
    intro t ht
    simpa only [v,dif_pos ht] using (henergy t ht).choose_spec.1
  have hv : ∀ t, T ≤ t → v t ≤ -q (X t) := by
    intro t ht
    simpa only [v,dif_pos ht] using (henergy t ht).choose_spec.2
  have hnonneg : ∀ t, T ≤ t → 0 ≤ q (X t) := fun t ht => hq0 _ (hXK t ht)
  obtain ⟨L,hL⟩ := potential_tendsto_of_bounded_dissipation (fun t => P (X t)) v
    (fun t => q (X t)) T M hdv hv hnonneg (fun t ht => hM (mem_image_of_mem _ (hXK t ht)))
  exact dissipation_tendsto_zero _ _ _ T L hdv hv hnonneg hu hL

end CoreCouplingGlobal
