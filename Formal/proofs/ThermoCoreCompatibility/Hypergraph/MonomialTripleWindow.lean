import proofs.ThermoCoreCompatibility.Hypergraph.MonomialTripleSource

namespace ThermoCoreCompatibility.Hypergraph.MonomialTriple

noncomputable def windowData (u l : ℝ) (hu : 71/100 ≤ u)
    (hl : 81/125 ≤ l) (hlu : l ≤ 13/20) : FanData (Fin 3) :=
  { data with
    lower := ![13/20,l,13/20]
    upper := ![u,19/25,19/25]
    lower_pos := by
      intro i
      fin_cases i <;> norm_num
      linarith
    box_nonempty := by
      intro i
      fin_cases i <;> norm_num
      · linarith
      · linarith }

theorem split_obstruction_window {a b : ℝ} (ha : 0 ≤ a)
    (h₀ : 5*b < 356/125+a) (h₁ : 243/125 < b+2*a^4)
    (h₂ : 2*a+3*a^3 < 5*b) : False := by
  by_cases h : a ≤ 7/8
  · have hp := pow_le_pow_left₀ ha h 4
    norm_num at hp
    linarith
  · have hge : (7/8 : ℝ) ≤ a := le_of_lt (lt_of_not_ge h)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7/8) hge 3
    norm_num at hp
    linarith

/-- A two-parameter region, not a single finely tuned counterexample. -/
theorem window_incompatible (u l : ℝ) (hu : 71/100 ≤ u) (hu' : u ≤ 89/125)
    (hl : 81/125 ≤ l) (hlu : l ≤ 13/20) :
    ¬ (windowData u l hu hl hlu).SourceCompatible Set.univ (1/10) (9/10) (1/10) (9/10) := by
  intro h
  obtain ⟨a,b,ha,_,_,_,c,hc,hp⟩ :=
    ((windowData u l hu hl hlu).sourceCompatible_iff Set.univ (1/10) (9/10) (1/10) (9/10)
      (by norm_num) (by norm_num)).1 h
  have h₀ := hp 0 (Set.mem_univ 0)
  have h₁ := hp 1 (Set.mem_univ 1)
  have h₂ := hp 2 (Set.mem_univ 2)
  have hc₀ := (hc 0).2
  have hc₁ := (hc 1).1
  norm_num [windowData,data] at h₀ h₁ h₂ hc₀ hc₁
  change TriangleProduction 3 1 1 (a^3) b (c 2) (a-b) at h₂
  obtain ⟨_,h₀,_⟩ := h₀
  obtain ⟨_,_,h₁⟩ := h₁
  obtain ⟨h₂a,_,h₂b⟩ := h₂
  apply split_obstruction_window (a := a) (b := b) (by linarith) <;> nlinarith

theorem window_deletions (u l : ℝ) (hu : 71/100 ≤ u)
    (hl : 81/125 ≤ l) (hlu : l ≤ 13/20) (i : Fin 3) :
    (windowData u l hu hl hlu).SourceCompatible {k | k ≠ i} (1/10) (9/10) (1/10) (9/10) := by
  obtain ⟨z,hz,ha,hau,hb,hbu,hc,hp⟩ := source_deletions i
  refine ⟨z,hz,ha,hau,hb,hbu,?_,hp⟩
  intro k
  have hh := hc k
  fin_cases k <;> norm_num [windowData,data] at hh ⊢
  · exact ⟨hh.1,le_trans hh.2 hu⟩
  · exact ⟨le_trans hlu hh.1,hh.2⟩
  · exact hh

theorem minimal_triple_parameter_region (u l : ℝ)
    (hu : 71/100 ≤ u) (hu' : u ≤ 89/125) (hl : 81/125 ≤ l) (hlu : l ≤ 13/20) :
    (¬ (windowData u l hu hl hlu).SourceCompatible Set.univ (1/10) (9/10) (1/10) (9/10)) ∧
      ∀ i : Fin 3, (windowData u l hu hl hlu).SourceCompatible {k | k ≠ i}
        (1/10) (9/10) (1/10) (9/10) :=
  ⟨window_incompatible u l hu hu' hl hlu,window_deletions u l hu hl hlu⟩

end ThermoCoreCompatibility.Hypergraph.MonomialTriple
