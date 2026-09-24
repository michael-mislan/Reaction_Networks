import proofs.RAFQueryCompilation.ClosureCertificate

namespace RAFQueryCompilation
open RAF

variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Check terminal closedness without constructing the union of enabled outputs. -/
def closedPool (Q : CRS M R) (S : Finset R) (pool : Finset M) : Bool :=
  decide (∀ r ∈ S, Q.inputs r ⊆ pool → Q.outputs r ⊆ pool)

omit [DecidableEq R] in
theorem closedPool_iff (Q : CRS M R) (S : Finset R) (pool : Finset M) :
    closedPool Q S pool = true ↔ closureStep Q S pool = pool := by
  simp only [closedPool,decide_eq_true_eq]
  constructor
  · intro h
    apply Finset.Subset.antisymm _ Finset.subset_union_left
    intro x hx
    simp only [Finset.mem_union,Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨r,hr,hx⟩
    · exact hx
    · split_ifs at hx with he
      · exact h r hr he hx
      · simp at hx
  · intro h r hr he x hx
    rw [← h]
    simp only [closureStep,Finset.mem_union,Finset.mem_biUnion]
    right
    exact ⟨r,hr,by simpa [Enabled,he] using hx⟩

def checkClosureWithoutUnion [Fintype M] (Q : CRS M R) (S : Finset R)
    (order : List R) : Option (Finset M) :=
  let pool := replaySchedule Q S order
  if closedPool Q S pool then some pool else none

theorem checkClosureWithoutUnion_eq [Fintype M] (Q : CRS M R) (S : Finset R)
    (order : List R) : checkClosureWithoutUnion Q S order = checkClosure Q S order := by
  simp only [checkClosureWithoutUnion,checkClosure,closedPool_iff]

end RAFQueryCompilation
