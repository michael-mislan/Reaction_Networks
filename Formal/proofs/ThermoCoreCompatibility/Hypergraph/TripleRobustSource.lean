import proofs.ThermoCoreCompatibility.Hypergraph.TriplePerturbation

namespace ThermoCoreCompatibility.Hypergraph.MonomialTriple

private theorem near_interval {l u l' u' x : ℝ}
    (hl : |l'-l| ≤ 1/1000000) (hu : |u'-u| ≤ 1/1000000)
    (hx : l+1/100000 ≤ x ∧ x ≤ u-1/100000) : l' ≤ x ∧ x ≤ u' := by
  rw [abs_le] at hl hu
  constructor <;> linarith

theorem robust_source_incompatible (D : FanData (Fin 3)) (la ua lb ub : ℝ)
    (hn : Near D la ua lb ub) : ¬ D.SourceCompatible Set.univ la ua lb ub := by
  have hncopy := hn
  obtain ⟨hg,h₀,h₁,h₂,hl,hu,hla,hua,hlb,hub⟩ := hn
  have hla' := abs_le.mp hla
  have hua' := abs_le.mp hua
  have hlb' := abs_le.mp hlb
  have hub' := abs_le.mp hub
  intro hh
  obtain ⟨A,B,ha,hau,hb,hbu,C,hc,hp⟩ :=
    (D.sourceCompatible_iff _ la ua lb ub (by linarith) (by linarith)).1 hh
  have hac : 0 ≤ A := by linarith
  have hau' : A ≤ 1 := by linarith
  have hbc : 0 ≤ B := by linarith
  have hbu' : B ≤ 1 := by linarith
  have hcc : ∀ i, 0 ≤ C i ∧ C i ≤ 1 := by
    intro i
    have hl' := abs_le.mp (hl i)
    have hu' := abs_le.mp (hu i)
    have hci := hc i
    fin_cases i <;> norm_num [data] at hl' hu' hci ⊢ <;> constructor <;> linarith
  have hres : ∀ i k, -(5*(1/1000000)) < residual data A B C i k := by
    intro i k
    have herr := residual_error D la ua lb ub A B C hncopy hac hau' hbc hbu' hcc i k
    have hpos := (residual_positive_iff D A B C i).2 (hp i (Set.mem_univ i)) k
    have ht := residual_transfer herr
    linarith
  have hc₀ : C 0 ≤ 89/125 := by
    have hh := abs_le.mp (hu 0)
    have hc' := (hc 0).2
    norm_num [data] at hh
    linarith
  have hc₁ : 81/125 ≤ C 1 := by
    have hh := abs_le.mp (hl 1)
    have hc' := (hc 1).1
    norm_num [data] at hh
    linarith
  have h01 := hres 0 1
  have h12 := hres 1 2
  have h20 := hres 2 0
  have h22 := hres 2 2
  change -(5*(1/1000000)) < 1*(A-B)-4*(B-C 0) at h01
  change -(5*(1/1000000)) < (1/2)*(B-C 1)-1*(C 1-A^4) at h12
  change -(5*(1/1000000)) < (3:ℕ)*(1*(C 2-A^3))-1*(A-B) at h20
  change -(5*(1/1000000)) < 1*(B-C 2)-1*(C 2-A^3) at h22
  have hm := source_coordinate_margin (B := B) (C₂ := C 2) (τ := -(5*(1/1000000))) hac hc₀ hc₁
    (by linarith) (by linarith) (by linarith) (by linarith)
  norm_num at hm

theorem stable_source_witness (D : FanData (Fin 3)) (la ua lb ub A B : ℝ)
    (C : Fin 3 → ℝ) (F : Set (Fin 3)) (hn : Near D la ua lb ub)
    (ha : 1/10+1/100000 ≤ A ∧ A ≤ 9/10-1/100000)
    (hb : 1/10+1/100000 ≤ B ∧ B ≤ 9/10-1/100000)
    (hc : ∀ i, data.lower i+1/100000 ≤ C i ∧ C i ≤ data.upper i-1/100000)
    (hp : ∀ i ∈ F, ∀ k, 9/100000 < residual data A B C i k) :
    D.SourceCompatible F la ua lb ub := by
  have hncopy := hn
  obtain ⟨hg,h₀,h₁,h₂,hl,hu,hla,hua,hlb,hub⟩ := hn
  have hla' := abs_le.mp hla
  have hlb' := abs_le.mp hlb
  have hab := near_interval hla hua ha
  have hbb := near_interval hlb hub hb
  apply (D.sourceCompatible_iff _ la ua lb ub (by linarith) (by linarith)).2
  refine ⟨A,B,hab.1,hab.2,hbb.1,hbb.2,C,fun i => near_interval (hl i) (hu i) (hc i),?_⟩
  intro i hi
  apply (residual_positive_iff D A B C i).1
  intro k
  have hcc : ∀ j, 0 ≤ C j ∧ C j ≤ 1 := by
    intro j
    have hh := hc j
    fin_cases j <;> norm_num [data] at hh ⊢ <;> constructor <;> linarith
  exact robust_positive (hp i hi k)
    (residual_error D la ua lb ub A B C hncopy (by linarith) (by linarith)
      (by linarith) (by linarith) hcc i k)

theorem robust_source_deletions (D : FanData (Fin 3)) (la ua lb ub : ℝ)
    (hn : Near D la ua lb ub) : ∀ j : Fin 3, D.SourceCompatible {i | i ≠ j} la ua lb ub := by
  intro j
  fin_cases j
  · apply stable_source_witness D la ua lb ub (22/25) (157/200)
      ![7/10,13/20+1/100000,18/25] _ hn (by norm_num) (by norm_num)
    · norm_num [data,Fin.forall_fin_succ]
    · norm_num [residual,data,Fin.forall_fin_succ]
  · apply stable_source_witness D la ua lb ub (169/200) (88/125)
      ![67/100,7/10,653/1000] _ hn (by norm_num) (by norm_num)
    · norm_num [data,Fin.forall_fin_succ]
    · norm_num [residual,data,Fin.forall_fin_succ]
  · apply stable_source_witness D la ua lb ub (141/160) (93/125)
      ![71/100-1/100000,13/20+1/100000,7/10] _ hn (by norm_num) (by norm_num)
    · norm_num [data,Fin.forall_fin_succ]
    · norm_num [residual,data,Fin.forall_fin_succ]
      decide

theorem simultaneous_perturbation (D : FanData (Fin 3)) (la ua lb ub : ℝ)
    (hn : Near D la ua lb ub) :
    (¬ D.SourceCompatible Set.univ la ua lb ub) ∧
    ∀ j : Fin 3, D.SourceCompatible {i | i ≠ j} la ua lb ub :=
  ⟨robust_source_incompatible D la ua lb ub hn,robust_source_deletions D la ua lb ub hn⟩

end ThermoCoreCompatibility.Hypergraph.MonomialTriple
