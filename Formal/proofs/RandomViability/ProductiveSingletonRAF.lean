import proofs.RandomViability.LocalIncidenceClassification
import proofs.RandomViability.ProductiveRAF

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 40000

theorem productive_incidence_singleton_isRAF {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (r : Reaction n) (z : Molecule n) (h : ProductiveSingletonIncidence r z) (hsel : r ∈ c z) :
    IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig c) {r} := by
  let Q := binaryPolymerCRS n 2
  have hl : RevEnabledLhs Q Q.food r := by
    intro x hx
    rcases Finset.mem_insert.mp hx with he | he
    · subst x
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1⟩
    · have he' := Finset.mem_singleton.mp he
      subst x
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.1⟩
  have hfood : Q.food ⊆ revClosureAt Q {r} 1 := Finset.subset_union_left
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
    have he : s = r := Finset.mem_singleton.mp hs
    subst s
    exact ⟨1,Finset.union_subset (hl.trans hfood) hrhs⟩
  · intro s hs
    have he : s = r := Finset.mem_singleton.mp hs
    subst s
    refine ⟨z,1,?_,hsel⟩
    rcases h.2.2.2 with hz | hz
    · exact hfood (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)
    · simpa only [hz] using hp

def hasSingletonRAF {n : ℕ} (c : SourceMoleculeFibreConfig n) : Prop :=
  ∃ r : Reaction n,IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig c) {r}

end
end RandomViability
