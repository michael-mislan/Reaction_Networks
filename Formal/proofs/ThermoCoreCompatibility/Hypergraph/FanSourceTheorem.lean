import proofs.ThermoCoreCompatibility.Hypergraph.FanSource

namespace ThermoCoreCompatibility.Hypergraph

theorem FanData.sourceCompatible_iff {ι : Type*} [DecidableEq ι] [Fintype ι]
    (D : FanData ι) (F : Set ι) (la ua lb ub : ℝ) (hla : 0 < la) (hlb : 0 < lb) :
    D.SourceCompatible F la ua lb ub ↔
      ∃ a b, la ≤ a ∧ a ≤ ua ∧ lb ≤ b ∧ b ≤ ub ∧ D.LiteralWitness F a b := by
  constructor
  · rintro ⟨z,_,ha,hau,hb,hbu,hc,hp⟩
    refine ⟨z none,z (some none),ha,hau,hb,hbu,fun i => z (some (some i)),hc,?_⟩
    intro i hi
    exact ((D.triangle i).current_production_iff z).1 (hp i hi).1
  · rintro ⟨a,b,ha,hau,hb,hbu,c,hc,hp⟩
    let z : FanSpecies ι → ℝ := fun s => match s with
      | none => a
      | some none => b
      | some (some i) => c i
    have hz : ∀ s, 0 < z s := by
      intro s
      rcases s with _ | (_ | i)
      · exact lt_of_lt_of_le hla ha
      · exact lt_of_lt_of_le hlb hb
      · exact lt_of_lt_of_le (D.lower_pos i) (hc i).1
    refine ⟨z,hz,ha,hau,hb,hbu,hc,?_⟩
    intro i hi
    have hprod : (D.triangle i).motif.Productive (D.network.current z) :=
      ((D.triangle i).current_production_iff z).2 (hp i hi)
    refine ⟨hprod,?_⟩
    have hh := ((D.triangle i).productive_iff (D.network.current z)).1 hprod
    have hm : (1 : ℝ) ≤ (D.triangle i).gain := by
      have hh := D.gain_ge_two i
      change (1 : ℝ) ≤ (D.gain i : ℝ)
      exact_mod_cast (by omega : 1 ≤ D.gain i)
    have hpos := triangle_currents_positive hm hh.1 hh.2.1 hh.2.2
    intro r hr
    simp only [TriangleIn.motif,Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact hpos.1
    · exact hpos.2.1
    · exact hpos.2.2

/-- Source-level bounded fan theorem. Every branch is an inherited-definition
PAC by source_isPAC; directions are included and reconstructed, not dropped. -/
theorem FanData.sourceCompatible_univariate_iff {ι : Type*}
    [DecidableEq ι] [Fintype ι] [Nonempty ι] (D : FanData ι)
    (la ua lb ub : ℝ) (hla : 0 < la) (hlb : 0 < lb) (hbox : lb ≤ ub) :
    D.SourceCompatible Set.univ la ua lb ub ↔
      ∃ a, la ≤ a ∧ a ≤ ua ∧ D.UnivariateConditions a lb ub := by
  rw [D.sourceCompatible_iff Set.univ la ua lb ub hla hlb]
  exact D.boundedFan_univariate_iff la ua lb ub hbox

theorem FanData.sourceCompatible_mono {ι : Type*} [DecidableEq ι] [Fintype ι]
    (D : FanData ι) {F G : Set ι} {la ua lb ub : ℝ} (hFG : F ⊆ G)
    (h : D.SourceCompatible G la ua lb ub) : D.SourceCompatible F la ua lb ub := by
  obtain ⟨z,hz,ha,hau,hb,hbu,hc,hp⟩ := h
  exact ⟨z,hz,ha,hau,hb,hbu,hc,fun i hi => hp i (hFG hi)⟩

theorem FanData.sourceCompatible_empty {ι : Type*} [DecidableEq ι] [Fintype ι]
    (D : FanData ι) (la ua lb ub : ℝ) (hla : 0 < la) (hlb : 0 < lb)
    (ha : la ≤ ua) (hb : lb ≤ ub) : D.SourceCompatible ∅ la ua lb ub := by
  apply (D.sourceCompatible_iff ∅ la ua lb ub hla hlb).2
  exact ⟨la,lb,le_rfl,ha,le_rfl,hb,D.lower,
    fun i => ⟨le_rfl,D.box_nonempty i⟩,fun _ hi => hi.elim⟩

end ThermoCoreCompatibility.Hypergraph
