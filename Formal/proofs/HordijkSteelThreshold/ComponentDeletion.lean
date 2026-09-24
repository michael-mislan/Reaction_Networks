import proofs.HordijkSteelThreshold.FoodChunkGraph

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

def deletionPool {n : Nat} (rank : Molecule n → Nat) (t : Nat) :
    Finset (Molecule n) := Finset.univ.filter (fun x => t ≤ rank x)

def deletionBlock {n : Nat} (rank : Molecule n → Nat) (t : Nat) :
    Finset (Molecule n) := Finset.univ.filter (fun x => rank x = t)

noncomputable def poolEnabledEdges {n : Nat} (Cat : Molecule n → Reaction n → Prop)
    (S : Finset (Reaction n)) (C : Finset (Molecule n)) : Finset (Reaction n) := by
  classical
  exact S.filter (fun r => ∃ x ∈ C, Cat x r)

/-- Every deleted block is closed under the graph edges enabled by the pool
present at its deletion. A connected component has this property. The rank
of an undeleted molecule is at least the horizon. -/
def ComponentDeletionClosed {n : Nat} (L : Nat)
    (Cat : Molecule n → Reaction n → Prop) (S : Finset (Reaction n))
    (rank : Molecule n → Nat) (horizon : Nat) : Prop :=
  ∀ t < horizon, foodChunkGraphStep L
    (poolEnabledEdges Cat S (deletionPool rank t)) (deletionBlock rank t) ⊆
      deletionBlock rank t

def deletionForbiddenEdges {n : Nat} (L : Nat) (S : Finset (Reaction n))
    (rank : Molecule n → Nat) (horizon : Nat) : Finset (Reaction n) :=
  S.filter (fun r =>
    (rank (foodChunkOther L r) < horizon ∨ rank (reactionProduct r) < horizon) ∧
    rank (foodChunkOther L r) ≠ rank (reactionProduct r))

theorem product_mem_foodChunkGraphStep {n L : Nat} {S : Finset (Reaction n)}
    {A : Finset (Molecule n)} {r : Reaction n} (hr : r ∈ S)
    (ha : foodChunkOther L r ∈ A) :
    reactionProduct r ∈ foodChunkGraphStep L S A := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨r, hr, Finset.mem_union_left _ ?_⟩
  simp [ha]

theorem other_mem_foodChunkGraphStep {n L : Nat} {S : Finset (Reaction n)}
    {A : Finset (Molecule n)} {r : Reaction n} (hr : r ∈ S)
    (ha : reactionProduct r ∈ A) :
    foodChunkOther L r ∈ foodChunkGraphStep L S A := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨r, hr, Finset.mem_union_right _ ?_⟩
  simp [ha]

/-- A deletion prefix closes all catalyst coordinates from the known remaining
pool into nonexempt edges. Edges internal to a single deleted block are exempt;
ignoring that exemption would give a false probability exponent. -/
theorem componentDeletion_forbidden_absent {n L horizon : Nat}
    {Cat : Molecule n → Reaction n → Prop} {S : Finset (Reaction n)}
    {rank : Molecule n → Nat}
    (hc : ComponentDeletionClosed L Cat S rank horizon)
    {x : Molecule n} (hx : x ∈ deletionPool rank horizon)
    {r : Reaction n} (hr : r ∈ deletionForbiddenEdges L S rank horizon) :
    ¬ Cat x r := by
  classical
  intro hcat
  have hxr : horizon ≤ rank x := (Finset.mem_filter.mp hx).2
  obtain ⟨hrS, hlow, hne⟩ := Finset.mem_filter.mp hr
  rcases lt_or_gt_of_ne hne with hab | hba
  · have ht : rank (foodChunkOther L r) < horizon := by omega
    have hxp : x ∈ deletionPool rank (rank (foodChunkOther L r)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hren : r ∈ poolEnabledEdges Cat S
        (deletionPool rank (rank (foodChunkOther L r))) := by
      exact Finset.mem_filter.mpr ⟨hrS, x, hxp, hcat⟩
    have ha : foodChunkOther L r ∈ deletionBlock rank (rank (foodChunkOther L r)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hb := hc _ ht (product_mem_foodChunkGraphStep hren ha)
    have heq := (Finset.mem_filter.mp hb).2
    omega
  · have ht : rank (reactionProduct r) < horizon := by omega
    have hxp : x ∈ deletionPool rank (rank (reactionProduct r)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hren : r ∈ poolEnabledEdges Cat S
        (deletionPool rank (rank (reactionProduct r))) := by
      exact Finset.mem_filter.mpr ⟨hrS, x, hxp, hcat⟩
    have ha : reactionProduct r ∈ deletionBlock rank (rank (reactionProduct r)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hb := hc _ ht (other_mem_foodChunkGraphStep hren ha)
    have heq := (Finset.mem_filter.mp hb).2
    omega

end HordijkSteelThreshold
