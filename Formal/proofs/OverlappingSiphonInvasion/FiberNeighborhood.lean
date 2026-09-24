import proofs.OverlappingSiphonInvasion.NormalizedGrowth

noncomputable section
open Set Filter Topology
namespace OverlappingSiphonInvasion

/-- Compactness turns positivity on the entire fiber into a uniform positive
bound over nearby projections, including when the fiber is empty. -/
theorem compact_fiber_positive_neighborhood (K : Set LiftState) (hK : IsCompact K)
    (G : LiftState → ℝ) (hG : Continuous G) (y : State)
    (hp : ∀ z ∈ K, z.1 = y → 0 < G z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 y, ∀ z ∈ K, z.1 = x → δ < G z := by
  let F := K ∩ {z : LiftState | z.1 = y}
  have hF : IsCompact F := hK.inter_right (isClosed_eq continuous_fst continuous_const)
  obtain ⟨δ,hδ,hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ F, δ < G z := by
    by_cases hn : F.Nonempty
    · obtain ⟨z,hz,hmin⟩ := hF.exists_isMinOn hn hG.continuousOn
      have hpz := hp z hz.1 hz.2
      refine ⟨G z/2,by linarith,?_⟩
      intro w hw
      have hh : G z ≤ G w := hmin hw
      linarith
    · refine ⟨1,by norm_num,?_⟩
      intro z hz
      exact (hn ⟨z,hz⟩).elim
  let B := K ∩ {z | G z ≤ δ}
  have hB : IsCompact B := hK.inter_right (isClosed_le hG continuous_const)
  have hc : IsClosed (Prod.fst '' B) := (hB.image continuous_fst).isClosed
  have hy : y ∈ (Prod.fst '' B)ᶜ := by
    rintro ⟨z,hz,hzy⟩
    exact (not_le_of_gt (hδF z ⟨hz.1,hzy⟩)) hz.2
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hc.isOpen_compl.mem_nhds hy] with x hx
  intro z hz hzx
  apply lt_of_not_ge
  intro hh
  exact hx ⟨z,⟨hz,hh⟩,hzx⟩

/-- Source-projection convergence suffices; the normalized directions need not
converge. This is the compact-fiber step used by the boundary growth argument. -/
theorem normalized_eventual_growth_of_projection_limit (p : Rates) (ru rv rj R : ℝ)
    (k : ℕ) (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj)
    (X : ℝ → LiftState) (hX : ∀ t, 0 ≤ t → X t ∈ physicalLiftClosure ru rv rj R)
    (y : State) (hy : Tendsto (fun t => (X t).1) atTop (𝓝 y))
    (hp : ∀ z ∈ physicalLiftClosure ru rv rj R, z.1 = y →
      0 < normalGrowth p ru rv rj k z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ t in atTop, δ < normalGrowth p ru rv rj k (X t) := by
  have hc : Continuous (normalGrowth p ru rv rj k) := by
    unfold normalGrowth normalHU normalHV normalHJ privateA privateB sharedC
    fun_prop
  obtain ⟨δ,hδ,hn⟩ := compact_fiber_positive_neighborhood _
    (physicalLiftClosure_isCompact ru rv rj R hru hrv hrj) _ hc y hp
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hy.eventually hn,eventually_ge_atTop (0:ℝ)] with t ht ht0
  exact ht (X t) (hX t ht0) rfl

end OverlappingSiphonInvasion
