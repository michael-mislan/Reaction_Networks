import proofs.ThermoCoreCompatibility.Hypergraph.Main
import proofs.ThermoCoreCompatibility.Hypergraph.UnboundedMonomialOrder
import proofs.ThermoCoreCompatibility.Hypergraph.TripleRobustSource

namespace ThermoCoreCompatibility.Hypergraph

structure ReviewedResolution : Prop where
  original : TCCHResolution
  unbounded_order : ∀ (L : ℕ) (hL : 2 ≤ L),
    (∀ e, ((Shortcut.assembly L hL).motif e).IsPAC) ∧
    (¬ ∃ z : Fin (L+1) → ℝ, (∀ i, 0 < z i) ∧
      ∀ e, ((Shortcut.assembly L hL).motif e).Productive ((Shortcut.assembly L hL).network.current z)) ∧
    (∀ F, F ≠ Set.univ → Shortcut.Compatible L hL F) ∧
    (∃ z : Fin (L+1) → ℝ, (∀ i, 9/10 ≤ z i ∧ z i ≤ 1) ∧
      ∀ r, 0 < (Shortcut.assembly L hL).network.current z r) ∧
    (Shortcut.family L hL).LinearComplexCompatible ∧
    (∀ i, 9/10 ≤ Shortcut.complexValues L (atom i 1) ∧ Shortcut.complexValues L (atom i 1) ≤ 1) ∧
    (∀ i, 81/100 ≤ Shortcut.complexValues L (atom i 2) ∧ Shortcut.complexValues L (atom i 2) ≤ 1)
  robust_triple : ∀ (D : FanData (Fin 3)) (la ua lb ub : ℝ),
    MonomialTriple.Near D la ua lb ub →
      (¬ D.SourceCompatible Set.univ la ua lb ub) ∧
      ∀ j : Fin 3, D.SourceCompatible {i | i ≠ j} la ua lb ub

theorem reviewed_resolution : ReviewedResolution :=
  ⟨tcch_resolution,Shortcut.unbounded_monomial_order,MonomialTriple.simultaneous_perturbation⟩

end ThermoCoreCompatibility.Hypergraph
