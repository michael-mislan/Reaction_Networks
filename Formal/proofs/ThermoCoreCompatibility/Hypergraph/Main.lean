import proofs.ThermoCoreCompatibility.Hypergraph.MonomialTripleWindow
import proofs.ThermoCoreCompatibility.Hypergraph.RingSource
import proofs.ThermoCoreCompatibility.Hypergraph.GradedSource

/-! Thermodynamic compatibility hypergraph of autocatalytic cores.

This root assembles source-level bounded fan elimination, unbounded minimal
hyperedge order, a minimal triple surviving both earlier feasibility layers,
a nondegenerate forbidden-family parameter region, and common-state gluing
on a graded multi-interface class. It does not assert a classification of all
finite reaction networks or any statement about eventual dynamical activity.
-/

namespace ThermoCoreCompatibility.Hypergraph

structure TCCHResolution : Prop where
  bounded_fan : ∀ (ι : Type) [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (D : FanData ι) (la ua lb ub : ℝ), 0 < la → 0 < lb → lb ≤ ub →
      (D.SourceCompatible Set.univ la ua lb ub ↔
        ∃ a, la ≤ a ∧ a ≤ ua ∧ D.UnivariateConditions a lb ub)
  arbitrary_ring_order : ∀ (n : ℕ) [NeZero n] [Fact (1 < n)],
    (∀ i : ZMod n, (Ring.motif n i).IsPAC) ∧
      (¬ Ring.Compatible n Set.univ) ∧
      ∀ j : ZMod n, Ring.Compatible n {i | i ≠ j}
  monomial_minimal_triple :
    (¬ MonomialTriple.data.SourceCompatible Set.univ (1/10) (9/10) (1/10) (9/10)) ∧
      (∀ i : Fin 3, MonomialTriple.data.SourceCompatible {k | k ≠ i}
        (1/10) (9/10) (1/10) (9/10)) ∧
      MonomialTriple.family.DirectionCompatible ∧
      MonomialTriple.family.LinearComplexCompatible
  forbidden_parameter_region : ∀ (u l : ℝ) (hu : 71/100 ≤ u) (_hu' : u ≤ 89/125)
    (hl : 81/125 ≤ l) (hlu : l ≤ 13/20),
    (¬ (MonomialTriple.windowData u l hu hl hlu).SourceCompatible Set.univ
      (1/10) (9/10) (1/10) (9/10)) ∧
      ∀ i : Fin 3, (MonomialTriple.windowData u l hu hl hlu).SourceCompatible {k | k ≠ i}
        (1/10) (9/10) (1/10) (9/10)
  graded_source_gluing : ∀ (V E : Type) [DecidableEq V] [DecidableEq E] [Fintype V]
    (G : PairAssembly V E) (rank : V → ℕ) (height : ℕ),
    (∀ v, rank v ≤ height) → (∀ e, rank (G.dst e) = rank (G.src e)+1) →
    ∃ z : V → ℝ, (∀ v, 9/10 ≤ z v ∧ z v ≤ 1) ∧
      (∀ e, (G.motif e).IsPAC ∧ (G.motif e).Productive (G.network.current z)) ∧
      ∀ r, 0 < G.network.current z r

/-- The source-integrated critical theorem package. -/
theorem tcch_resolution : TCCHResolution where
  bounded_fan := fun _ _ _ _ D la ua lb ub hla hlb hbox =>
    D.sourceCompatible_univariate_iff la ua lb ub hla hlb hbox
  arbitrary_ring_order := fun n _ _ =>
    ⟨Ring.source_isPAC n,Ring.source_full_incompatible n,Ring.source_deletion n⟩
  monomial_minimal_triple :=
    ⟨MonomialTriple.source_full_incompatible,MonomialTriple.source_deletions,
      MonomialTriple.source_directionCompatible,MonomialTriple.source_linearComplexCompatible⟩
  forbidden_parameter_region := MonomialTriple.minimal_triple_parameter_region
  graded_source_gluing := fun _ _ _ _ _ G rank height hb he =>
    G.graded_source_compatible rank height hb he

end ThermoCoreCompatibility.Hypergraph
