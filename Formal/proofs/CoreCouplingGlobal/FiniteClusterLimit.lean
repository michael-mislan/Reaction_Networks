import Mathlib

namespace CoreCouplingGlobal
open Set Filter Topology

/-- A continuous precompact real-time curve with finitely many possible cluster points converges. -/
theorem finite_cluster_limit {E : Type*} [TopologicalSpace E] [T2Space E] [NormalSpace E]
    (K S : Set E) (hK : IsCompact K) (hS : S.Finite) (X : ℝ → E) (T : ℝ)
    (hX : ContinuousOn X (Ici T)) (hmem : ∀ᶠ t in atTop, X t ∈ K)
    (hcluster : ∀ x ∈ K, MapClusterPt x atTop X → x ∈ S) :
    ∃ x ∈ K ∩ S, Tendsto X atTop (𝓝 x) := by
  obtain ⟨y,hyK,hy⟩ := hK.exists_mapClusterPt (le_principal_iff.2 (mem_map.2 hmem))
  have hyS := hcluster y hyK hy
  refine ⟨y,⟨hyK,hyS⟩,hK.tendsto_nhds_of_unique_mapClusterPt hmem ?_⟩
  intro z hzK hz
  by_contra hzy
  have hzS := hcluster z hzK hz
  have hdis : Disjoint ({y} : Set E) (S \ {y}) := by simp
  obtain ⟨U,V,hU,hV,hyU,hSV,hUV⟩ :=
    normal_separation isClosed_singleton (hS.diff (t := {y})).isClosed hdis
  have hyU' : y ∈ U := hyU (mem_singleton y)
  have hzV : z ∈ V := hSV ⟨hzS,hzy⟩
  have hcover : S ⊆ U ∪ V := by
    intro x hx
    by_cases hxy : x = y
    · subst x; exact Or.inl hyU'
    · exact Or.inr (hSV ⟨hx,hxy⟩)
  have hevent : ∀ᶠ t in atTop, X t ∈ U ∪ V :=
    (hK.tendsto_nhdsSet_of_mapClusterPt hmem hcluster)
      ((hU.union hV).mem_nhdsSet.2 hcover)
  obtain ⟨N,hN⟩ := eventually_atTop.1 hevent
  let R := max T N
  have htail : X '' Ici R ⊆ U ∪ V := by
    rintro _ ⟨t,ht,rfl⟩
    exact hN t (le_trans (le_max_right T N) ht)
  have hconn : IsPreconnected (X '' Ici R) :=
    isPreconnected_Ici.image X (hX.mono (Ici_subset_Ici.2 (le_max_left T N)))
  have hyfreq := hy.frequently (hU.mem_nhds hyU')
  obtain ⟨t,ht,htU⟩ := (hyfreq.and_eventually (eventually_ge_atTop R)).exists
  have hmeet : ((X '' Ici R) ∩ U).Nonempty := ⟨X t,⟨⟨t,htU,rfl⟩,ht⟩⟩
  have hinside : X '' Ici R ⊆ U := hconn.subset_left_of_subset_union hU hV hUV htail hmeet
  have hzfreq := hz.frequently (hV.mem_nhds hzV)
  obtain ⟨s,hs,hsR⟩ := (hzfreq.and_eventually (eventually_ge_atTop R)).exists
  exact Set.disjoint_left.1 hUV (hinside ⟨s,hsR,rfl⟩) hs

end CoreCouplingGlobal
