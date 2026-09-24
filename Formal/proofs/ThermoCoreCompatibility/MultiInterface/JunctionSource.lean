import proofs.ThermoCoreCompatibility.MultiInterface.JunctionAssembly
import proofs.ThermoCoreCompatibility.MultiInterface.PathEdges
import proofs.ThermoCoreCompatibility.MultiInterface.WeightedSource

namespace ThermoCoreCompatibility.MultiInterface

/-- An orientation of a simple graph, supplied together with its private-path
decomposition. The second condition rules out duplicates and antiparallel edges. -/
structure SourceAssembly (V I : Type*) where
  assembly : JunctionAssembly V I
  distinct : ∀ i e, assembly.vertex i ((assembly.path i).edgeSource e) ≠
    assembly.vertex i ((assembly.path i).edgeTarget e)
  simple : ∀ (e f : Σ i, (assembly.path i).Edge),
    ((assembly.vertex e.1 ((assembly.path e.1).edgeSource e.2) =
        assembly.vertex f.1 ((assembly.path f.1).edgeSource f.2) ∧
      assembly.vertex e.1 ((assembly.path e.1).edgeTarget e.2) =
        assembly.vertex f.1 ((assembly.path f.1).edgeTarget f.2)) ∨
     (assembly.vertex e.1 ((assembly.path e.1).edgeSource e.2) =
        assembly.vertex f.1 ((assembly.path f.1).edgeTarget f.2) ∧
      assembly.vertex e.1 ((assembly.path e.1).edgeTarget e.2) =
        assembly.vertex f.1 ((assembly.path f.1).edgeSource f.2))) → e = f

namespace SourceAssembly

variable {V I : Type*} (S : SourceAssembly V I)

abbrev Edges := Σ i, (S.assembly.path i).Edge

def graph : Hypergraph.PairAssembly V S.Edges where
  src := fun e => S.assembly.vertex e.1 ((S.assembly.path e.1).edgeSource e.2)
  dst := fun e => S.assembly.vertex e.1 ((S.assembly.path e.1).edgeTarget e.2)
  distinct := fun e => S.distinct e.1 e.2

def factors (e : S.Edges) : Factors := (S.assembly.path e.1).edgeFactors e.2

variable [DecidableEq V] [DecidableEq S.Edges] [Fintype V]

def Compatible (ell : ℝ) (lo hi : {v // S.assembly.junction v} → ℝ) : Prop :=
  ∃ z : V → ℝ, (∀ v, ell ≤ z v ∧ z v ≤ 1) ∧
    (∀ v : {v // S.assembly.junction v}, lo v ≤ z v ∧ z v ≤ hi v) ∧
    ∀ e, (WeightedSource.motif S.graph S.factors e).IsPAC ∧
      (WeightedSource.motif S.graph S.factors e).Productive
        ((WeightedSource.network S.graph S.factors).current z)

theorem compatible_iff_literal (ell : ℝ) (lo hi : {v // S.assembly.junction v} → ℝ) :
    S.Compatible ell lo hi ↔ S.assembly.Compatible ell lo hi := by
  constructor
  · rintro ⟨z,hb,hj,hp⟩
    refine ⟨z,hb,hj,?_⟩
    intro i
    apply (Path.productiveState_iff_edges _ _).2
    intro e
    exact (WeightedSource.current_productive_iff S.graph S.factors ⟨i,e⟩ z).1 (hp ⟨i,e⟩).2
  · rintro ⟨z,hb,hj,hp⟩
    refine ⟨z,hb,hj,?_⟩
    rintro ⟨i,e⟩
    refine ⟨WeightedSource.isPAC S.graph S.factors ⟨i,e⟩,?_⟩
    apply (WeightedSource.current_productive_iff S.graph S.factors ⟨i,e⟩ z).2
    exact (Path.productiveState_iff_edges _ _).1 (hp i) e

end SourceAssembly

theorem sourceCompatible_iff_junctionFeasible {V I : Type*} (S : SourceAssembly V I)
    [DecidableEq V] [DecidableEq S.Edges] [Fintype V]
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell < 1)
    (lo hi : {v // S.assembly.junction v} → ℝ)
    (hlo : ∀ v, ell ≤ lo v) (hhi : ∀ v, hi v ≤ 1) :
    S.Compatible ell lo hi ↔ S.assembly.Feasible lo hi :=
  (S.compatible_iff_literal ell lo hi).trans
    (S.assembly.compatible_iff_feasible ell hell hell1 lo hi hlo hhi)

end ThermoCoreCompatibility.MultiInterface
