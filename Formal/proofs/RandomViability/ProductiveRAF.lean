import proofs.RandomViability.ProductiveCandidate
import proofs.PowerLawSmallRAF.SourcePowerLawTraceProbability

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

/-- The productive reaction is a genuine reversible RAF under its single
charged incidence. Its catalyst is its generated nonfood product. -/
theorem productive_singleton_isRAF {n : ℕ} (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n)
    (hsel : productiveReaction hn ∈ c (reactionProduct (productiveReaction hn))) :
    IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig c) {productiveReaction hn} := by
  let r := productiveReaction hn
  let Q := binaryPolymerCRS n 2
  have hf := productive_reaction_food hn
  have hl : RevEnabledLhs Q Q.food r := by
    intro x hx
    rcases Finset.mem_insert.mp hx with he | he
    · subst x
      exact hf.1
    · have he' := Finset.mem_singleton.mp he
      subst x
      exact hf.2.1
  have hfood : Q.food ⊆ revClosureAt Q {r} 1 := by
    exact Finset.subset_union_left
  have hp : reactionProduct r ∈ revClosureAt Q {r} 1 := by
    change reactionProduct r ∈ revClosureStep Q {r} Q.food
    unfold revClosureStep
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨r,Finset.mem_singleton_self r,?_⟩
    apply Finset.mem_union_left
    rw [if_pos hl]
    exact Finset.mem_singleton_self _
  have hrhs : Q.rhs r ⊆ revClosureAt Q {r} 1 := by
    simpa only [Q,binaryPolymerCRS,Finset.singleton_subset_iff] using hp
  refine ⟨Finset.singleton_nonempty _,?_,?_⟩
  · intro s hs
    have he : s=r := Finset.mem_singleton.mp hs
    subst s
    exact ⟨1,Finset.union_subset (hl.trans hfood) hrhs⟩
  · intro s hs
    have he : s=r := Finset.mem_singleton.mp hs
    subst s
    exact ⟨reactionProduct r,1,hp,hsel⟩

end
end RandomViability
