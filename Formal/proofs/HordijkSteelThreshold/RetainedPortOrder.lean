import proofs.HordijkSteelThreshold.ComponentDeletion

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

/-- Catalysis into a reaction joining v directly to a retained graph vertex. -/
def RetainedPortCat {n : Nat} (L : Nat)
    (Cat : Molecule n → Reaction n → Prop) (S : Finset (Reaction n))
    (rank : Molecule n → Nat) (h : Nat) (x v : Molecule n) : Prop :=
  ∃ r ∈ S, Cat x r ∧
    ((v = foodChunkOther L r ∧ h ≤ rank (reactionProduct r)) ∨
      (v = reactionProduct r ∧ h ≤ rank (foodChunkOther L r)))

/-- Any such catalytic arc points strictly forward in deletion order. Thus
deleted vertices' retained-port catalytic graph admits a strict ranking. -/
theorem retainedPortCat_rank_lt {n L h : Nat}
    {Cat : Molecule n → Reaction n → Prop} {S : Finset (Reaction n)}
    {rank : Molecule n → Nat}
    (hc : ComponentDeletionClosed L Cat S rank h)
    {x v : Molecule n} (hv : rank v < h)
    (he : RetainedPortCat L Cat S rank h x v) : rank x < rank v := by
  classical
  by_contra hn
  have hxp : x ∈ deletionPool rank (rank v) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  obtain ⟨r, hr, hcat, hp⟩ := he
  have hren : r ∈ poolEnabledEdges Cat S (deletionPool rank (rank v)) :=
    Finset.mem_filter.mpr ⟨hr, x, hxp, hcat⟩
  have hvb : v ∈ deletionBlock rank (rank v) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  rcases hp with ⟨heq, hh⟩ | ⟨heq, hh⟩
  · have hb := hc _ hv (product_mem_foodChunkGraphStep hren (heq ▸ hvb))
    have hz := (Finset.mem_filter.mp hb).2
    omega
  · have hb := hc _ hv (other_mem_foodChunkGraphStep hren (heq ▸ hvb))
    have hz := (Finset.mem_filter.mp hb).2
    omega

end HordijkSteelThreshold
