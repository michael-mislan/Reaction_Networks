import proofs.RAFBiochemicalInterventions.BiochemicalResult
import proofs.RAFBiochemicalInterventions.SmallClassification
import proofs.RAFBiochemicalInterventions.PoolingEmbedding
import proofs.RAFBiochemicalInterventions.ParentRobust
import proofs.RAFBiochemicalInterventions.ParentClosed
import proofs.RAFBiochemicalInterventions.CutClosed

namespace RAFBiochemicalLiteral

/-- The parent maximum is the common least closed extension of L and H. -/
theorem parent_least_extensions :
    LeastClosedExtension ParentSource.rows ParentSource.food
      SmallSource.lower ParentClosed.maximum ∧
    LeastClosedExtension ParentSource.rows ParentSource.food
      SmallSource.rows ParentClosed.maximum := by
  have h : LeastClosedExtension ParentSource.rows ParentSource.food
      SmallSource.rows ParentClosed.maximum :=
    ⟨parent_closed_forces_small _ ParentClosed.closed, ParentClosed.sub,
      ParentClosed.closed, fun D _ hd _ => ParentClosed.forces D hd⟩
  exact ⟨(same_parent_closed_extensions _).mpr h, h⟩

/-- Final finite-source claims. Logical lists are compared extensionally.
The source parser and continuous kinetic interpretation are not hypotheses
or conclusions of this theorem. -/
theorem publication_result :
    MinimalCut ParentSource.rows ParentSource.food ParentSource.target ParentSource.cut ∧
    Capable (remaining ParentSource.rows ParentSource.cut) ParentSource.food 68 ∧
    (∀ S, Subrows S SmallSource.rows →
      (Irreducible S SmallSource.food ↔
        SameRows S [SmallSource.r0] ∨ SameRows S [SmallSource.r7])) ∧
    (∀ S, Subrows S SmallSource.rows → RAF S SmallSource.food →
      Generated S SmallSource.food 168 → SameRows S SmallSource.rows) ∧
    (∀ C, Subrows C SmallSource.rows →
      (ClosedRAF SmallSource.rows C SmallSource.food ↔
        SameRows C SmallSource.lower ∨ SameRows C SmallSource.rows)) ∧
    ((∀ S, (Subrows S SmallSource.rows ∧ Irreducible S SmallSource.food) ↔
        (Subrows S SmallSource.lower ∧ Irreducible S SmallSource.food)) ∧
      Capable SmallSource.rows SmallSource.food 168 ∧
      ¬ Capable SmallSource.lower SmallSource.food 168) ∧
    (∀ C, Subrows C PoolingClosed.rows →
      (ClosedRAF PoolingClosed.rows C SmallSource.food ↔ SameRows C PoolingClosed.rows)) ∧
    (LeastClosedExtension ParentSource.rows ParentSource.food
      SmallSource.lower ParentClosed.maximum ∧
      LeastClosedExtension ParentSource.rows ParentSource.food
      SmallSource.rows ParentClosed.maximum) ∧
    (∀ C, Subrows C ParentClosed.rows →
      (ClosedRAF ParentClosed.rows C ParentClosed.food ↔ SameRows C ParentClosed.maximum)) ∧
    (∀ C, Subrows C CutClosed.rows →
      (ClosedRAF CutClosed.rows C CutClosed.food ↔ SameRows C CutClosed.maximum)) ∧
    (∀ (F' : List Nat) (c : Nat → Formula),
      (∀ x ∈ F', x ∉ ParentSource.blocked) →
      ¬ Capable (remaining (ParentSource.rows.map (annotate c)) ParentSource.cut)
        F' ParentSource.target) ∧
    (∀ (F' : List Nat) (c : Nat → Formula),
      (∀ x ∈ ParentSource.food, x ∈ F') →
      (∀ x ∈ F', x ∉ ParentSource.blocked) → Weakens ParentSource.rows c →
      MinimalCut (ParentSource.rows.map (annotate c)) F' ParentSource.target ParentSource.cut ∧
      Capable (remaining (ParentSource.rows.map (annotate c)) ParentSource.cut) F' 68) ∧
    Capable (remaining ParentSource.rows ParentSource.cut)
      ParentRobust.rescueFood ParentSource.target ∧
    (∀ X Y, (∀ x ∈ X, x ∉ ParentSource.blocked) →
      FiringTrace (remaining ParentSource.rows ParentSource.cut) X Y →
      ∀ y ∈ Y, y ∉ ParentSource.blocked) := by
  exact ⟨ParentIntervention.valine_cut_minimal, ParentIntervention.methionine_preserved,
    SmallSource.irreducible_catalogue, SmallSource.target_forces_all,
    SmallSource.closed_catalogue, SmallSource.catalogue_information_loss,
    PoolingClosed.unique_closed, parent_least_extensions,
    ParentClosed.unique_closed, CutClosed.unique_closed,
    ParentRobust.annotation_independent, ParentRobust.robust_selective_minimal,
    ParentRobust.precursor_rescue, ParentRobust.firing_exclusion⟩

end RAFBiochemicalLiteral
