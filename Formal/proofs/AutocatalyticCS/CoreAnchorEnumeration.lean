import proofs.AutocatalyticCS.FiniteMinimality
import proofs.AutocatalyticCS.PathPackGenerator

/-!
The terminal finite-enumeration theorem.  The three algorithmic tests are
Booleans equipped with exact semantic specifications.  Thus an implementation
may use graph routines and rational certificates, while the theorem depends
only on their checked interfaces.
-/

namespace AutocatalyticCS

variable {C A : Type*} [Fintype C] [DecidableEq C]

/-- Proof-carrying exact filters for candidate validity, semipositivity, and
minimality. -/
structure ExactCoreFilters
    (graphOK semipositive minimal : C → Prop) where
  graphTest : C → Bool
  semipositiveTest : C → Bool
  minimalTest : C → Bool
  graph_exact : ∀ c, graphTest c = true ↔ graphOK c
  semipositive_exact : ∀ c, semipositiveTest c = true ↔ semipositive c
  minimal_exact : ∀ c, minimalTest c = true ↔ minimal c

namespace ExactCoreFilters

def accepts {graphOK semipositive minimal : C → Prop}
    (F : ExactCoreFilters graphOK semipositive minimal) (c : C) : Bool :=
  F.graphTest c && F.semipositiveTest c && F.minimalTest c

omit [Fintype C] [DecidableEq C] in
theorem accepts_iff {graphOK semipositive minimal : C → Prop}
    (F : ExactCoreFilters graphOK semipositive minimal) (c : C) :
    F.accepts c = true ↔ graphOK c ∧ semipositive c ∧ minimal c := by
  rw [accepts, Bool.and_eq_true, Bool.and_eq_true,
    F.graph_exact, F.semipositive_exact, F.minimal_exact]
  constructor
  · rintro ⟨⟨hg, hs⟩, hm⟩
    exact ⟨hg, hs, hm⟩
  · rintro ⟨hg, hs, hm⟩
    exact ⟨⟨hg, hs⟩, hm⟩

end ExactCoreFilters

/-- The Boolean form of the verified incremental-antichain criterion. -/
def incrementalCoreTest {D : Type*} [PartialOrder D]
    [DecidableRel (fun a b : D => a < b)]
    (goodTest : D → Bool) (known : Finset D) (d : D) : Bool :=
  goodTest d && decide (∀ c ∈ known, ¬ c < d)

theorem incrementalCoreTest_exact {D : Type*} [PartialOrder D] [Fintype D]
    [DecidableRel (fun a b : D => a < b)]
    (good : D → Prop) (goodTest : D → Bool) (known : Finset D) (d : D)
    (hgood : ∀ c, goodTest c = true ↔ good c)
    (hknown : ∀ c, c ∈ known ↔ IsCore good c ∧ c < d) :
    incrementalCoreTest goodTest known d = true ↔ IsCore good d := by
  rw [incrementalCoreTest, Bool.and_eq_true, hgood, decide_eq_true_eq]
  exact (incremental_minimality good (known : Set D) d hknown).symm

/-- The semantic target set of all CS cores in the finite candidate universe. -/
noncomputable def csCores (graphOK semipositive minimal : C → Prop) : Finset C :=
  by
    classical
    exact Finset.univ.filter fun c => graphOK c ∧ semipositive c ∧ minimal c

omit [DecidableEq C] in
theorem mem_csCores_iff {graphOK semipositive minimal : C → Prop} {c : C} :
    c ∈ csCores graphOK semipositive minimal ↔
      graphOK c ∧ semipositive c ∧ minimal c := by
  classical
  simp [csCores]

/-- Executable anchored enumeration.  `generated a c` is the finite generator
membership test around anchor `a`. -/
def coreAnchorEnum [Fintype A] [DecidableEq A]
    {graphOK semipositive minimal : C → Prop}
    (anchors : Finset A) (generated : A → C → Bool)
  (F : ExactCoreFilters graphOK semipositive minimal) : Finset C :=
  Finset.univ.filter fun c =>
    F.accepts c && decide (∃ a ∈ anchors, generated a c = true)

omit [DecidableEq C] in
theorem mem_coreAnchorEnum_iff [Fintype A] [DecidableEq A]
    {graphOK semipositive minimal : C → Prop}
    {anchors : Finset A} {generated : A → C → Bool}
    {F : ExactCoreFilters graphOK semipositive minimal} {c : C} :
    c ∈ coreAnchorEnum anchors generated F ↔
      graphOK c ∧ semipositive c ∧ minimal c ∧
        ∃ a ∈ anchors, generated a c = true := by
  rw [show c ∈ coreAnchorEnum anchors generated F ↔
      F.accepts c = true ∧
        decide (∃ a ∈ anchors, generated a c = true) = true by
    simp [coreAnchorEnum]]
  rw [F.accepts_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hg, hs, hm⟩, ha⟩
    exact ⟨hg, hs, hm, ha⟩
  · rintro ⟨hg, hs, hm, ha⟩
    exact ⟨⟨hg, hs, hm⟩, ha⟩

omit [DecidableEq C] in
/-- Exact soundness and completeness of ordinary-core anchored extraction.

`anchor_complete` is the ordinary-core containment theorem.  `generator_complete`
is supplied by the alternating-path-pack generator theorem.  Exact filters then
give set equality; `Finset` representation supplies termination and duplicate
elimination. -/
theorem coreAnchorEnum_eq_csCores_of_anchor_coverage [Fintype A] [DecidableEq A]
    {graphOK semipositive minimal : C → Prop}
    (anchors : Finset A) (generated : A → C → Bool)
    (F : ExactCoreFilters graphOK semipositive minimal)
    (contains : A → C → Prop)
    (anchor_complete : ∀ c, graphOK c → semipositive c → minimal c →
      ∃ a ∈ anchors, contains a c)
    (generator_complete : ∀ a ∈ anchors, ∀ c,
      graphOK c → semipositive c → minimal c → contains a c →
      generated a c = true) :
    coreAnchorEnum anchors generated F = csCores graphOK semipositive minimal := by
  ext c
  rw [mem_coreAnchorEnum_iff]
  rw [mem_csCores_iff]
  constructor
  · rintro ⟨hg, hs, hm, -⟩
    exact ⟨hg, hs, hm⟩
  · rintro ⟨hg, hs, hm⟩
    obtain ⟨a, ha, hac⟩ := anchor_complete c hg hs hm
    exact ⟨hg, hs, hm, a, ha, generator_complete a ha c hg hs hm hac⟩

omit [DecidableEq C] in
/-- Core-anchored enumeration from exactly the input promised in the problem:
a complete finite list of ordinary cores.  Finite descent supplies a contained
ordinary core for every target candidate, so anchor coverage is a conclusion,
not an additional premise. -/
theorem coreAnchorEnum_eq_csCores [Fintype A] [DecidableEq A] [PartialOrder A]
    {graphOK semipositive minimal : C → Prop}
    (ordinaryGood : A → Prop) (underlying : C → A)
    (anchors : Finset A) (generated : A → C → Bool)
    (F : ExactCoreFilters graphOK semipositive minimal)
    (ordinary_complete : ∀ a, a ∈ anchors ↔ IsCore ordinaryGood a)
    (underlying_autocatalytic : ∀ c, graphOK c → semipositive c → minimal c →
      ordinaryGood (underlying c))
    (generator_complete : ∀ a ∈ anchors, ∀ c,
      graphOK c → semipositive c → minimal c → a ≤ underlying c →
      generated a c = true) :
    coreAnchorEnum anchors generated F = csCores graphOK semipositive minimal := by
  apply coreAnchorEnum_eq_csCores_of_anchor_coverage anchors generated F
    (fun a c => a ≤ underlying c)
  · intro c hg hs hm
    obtain ⟨a, ha_le, ha_core⟩ :=
      exists_core_le ordinaryGood (underlying_autocatalytic c hg hs hm)
    exact ⟨a, (ordinary_complete a).2 ha_core, ha_le⟩
  · exact generator_complete

omit [DecidableEq C] in
/-- Honest finite-output bound.  In particular, evaluation terminates and the
`Finset` result cannot contain duplicate candidates. -/
theorem coreAnchorEnum_card_le [Fintype A] [DecidableEq A]
    {graphOK semipositive minimal : C → Prop}
    (anchors : Finset A) (generated : A → C → Bool)
    (F : ExactCoreFilters graphOK semipositive minimal) :
    (coreAnchorEnum anchors generated F).card ≤ Fintype.card C := by
  exact Finset.card_le_univ _

namespace SimpleGraph

open _root_.SimpleGraph

variable {X R : Type*} [Fintype X] [Fintype R]

/-- The actual Boolean generator-membership test furnished by the finite
alternating path-pack generator. -/
noncomputable def generatedByPathPacks
    {G : _root_.SimpleGraph (X ⊕ R)} (M M' : G.Subgraph) : Bool := by
  classical
  exact decide (M' ∈ anchoredMatchingGenerator M)

theorem generatedByPathPacks_eq_true_iff
    {G : _root_.SimpleGraph (X ⊕ R)} {M M' : G.Subgraph} :
    generatedByPathPacks M M' = true ↔ M' ∈ anchoredMatchingGenerator M := by
  classical
  simp [generatedByPathPacks]

/-- Graph-level specialization of the terminal theorem.  Unique ordinary-core
matchings and ambient bipartiteness discharge generator completeness using the
verified alternating-exchange theorem. -/
theorem matchingCoreAnchorEnum_eq_csCores
    {G : _root_.SimpleGraph (X ⊕ R)} [Fintype G.Subgraph]
    [DecidableEq G.Subgraph]
    {semipositive minimal : G.Subgraph → Prop}
    (ordinaryGood : G.Subgraph → Prop) (anchors : Finset G.Subgraph)
    (F : ExactCoreFilters Subgraph.IsMatching semipositive minimal)
    (ordinary_complete : ∀ a, a ∈ anchors ↔ IsCore ordinaryGood a)
    (underlying_autocatalytic : ∀ c, c.IsMatching → semipositive c → minimal c →
      ordinaryGood c)
    (unique_anchors : ∀ a ∈ anchors, Subgraph.IsUniqueMatching a)
    (bipartite : G.IsBipartiteWith {v | v.isLeft} {v | v.isRight}) :
    coreAnchorEnum anchors generatedByPathPacks F =
      csCores Subgraph.IsMatching semipositive minimal := by
  apply coreAnchorEnum_eq_csCores ordinaryGood id anchors generatedByPathPacks F
    ordinary_complete underlying_autocatalytic
  intro a ha c hc _hs _hm hac
  rw [generatedByPathPacks_eq_true_iff]
  exact mem_anchoredMatchingGenerator_of_unique
    (unique_anchors a ha) hc (Subgraph.verts_mono hac) bipartite

end SimpleGraph

end AutocatalyticCS
