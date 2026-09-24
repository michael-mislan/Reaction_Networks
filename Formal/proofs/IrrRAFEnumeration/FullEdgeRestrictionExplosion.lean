import proofs.IrrRAFEnumeration.FiniteDuality

namespace IrrRAFEnumeration

/-- The one-clause clutter whose unique edge is the whole ground set. -/
def fullEdgeFamily (k : Nat) : Finset (Finset (Fin k)) :=
  {Finset.univ}

/-- Its expected blocker: all singleton subsets of the ground set. -/
def singletonFamily (k : Nat) : Finset (Finset (Fin k)) :=
  Finset.univ.image fun i => {i}

theorem hits_fullEdge_iff_nonempty {k : Nat} (T : Finset (Fin k)) :
    Hits (fullEdgeFamily k) T ↔ T.Nonempty := by
  constructor
  · intro hT
    by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
    subst T
    exact hT Finset.univ (by simp [fullEdgeFamily]) (by simp)
  · rintro ⟨x, hx⟩ E hE
    simp only [fullEdgeFamily, Finset.mem_singleton] at hE
    subst E
    exact Finset.not_disjoint_iff.mpr ⟨x, hx, Finset.mem_univ x⟩

/-- A one-edge clutter has exactly the singleton minimal transversals. -/
theorem fullEdge_blocker_eq_singletons (k : Nat) :
    blocker (fullEdgeFamily k) = singletonFamily k := by
  classical
  ext T
  rw [mem_blocker]
  constructor
  · intro hT
    obtain ⟨x, hxT⟩ := (hits_fullEdge_iff_nonempty T).mp hT.1
    have hsingleHits : Hits (fullEdgeFamily k) {x} :=
      (hits_fullEdge_iff_nonempty {x}).mpr (by simp)
    have hTsingle : T ⊆ {x} := hT.2 hsingleHits (by simpa using hxT)
    have hEq : T = {x} := Finset.Subset.antisymm hTsingle (by simpa using hxT)
    subst T
    simp [singletonFamily]
  · intro hT
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hT
    refine ⟨(hits_fullEdge_iff_nonempty {x}).mpr (by simp), ?_⟩
    intro B hB hBsub
    obtain ⟨y, hyB⟩ := (hits_fullEdge_iff_nonempty B).mp hB
    have hyx : y = x := Finset.mem_singleton.mp (hBsub hyB)
    exact Finset.singleton_subset_iff.mpr (hyx ▸ hyB)

/-- The positive residual after setting every member of `Z` false. -/
def fullEdgeFalseResidual {k : Nat} (Z : Finset (Fin k)) :
    Finset (Finset (Fin k)) :=
  {Finset.univ \ Z}

theorem fullEdgeFalseResidual_injective {k : Nat} :
    Function.Injective (fullEdgeFalseResidual (k := k)) := by
  intro A B hAB
  have hcomp : (Finset.univ \ A : Finset (Fin k)) = Finset.univ \ B := by
    simpa [fullEdgeFalseResidual] using hAB
  ext x
  have hx := Finset.ext_iff.mp hcomp x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
  tauto

/-- All false-only partial assignments already give an exponential family of
distinct normalized positive residuals, even though the original dual pair
has one input edge and only `k` outputs. -/
def fullEdgeFalseResidualFamily (k : Nat) :
    Finset (Finset (Finset (Fin k))) :=
  Finset.univ.powerset.image fullEdgeFalseResidual

theorem fullEdgeFalseResidualFamily_card (k : Nat) :
    (fullEdgeFalseResidualFamily k).card = 2 ^ k := by
  classical
  rw [fullEdgeFalseResidualFamily,
    Finset.card_image_iff.mpr fun A _ B _ h => fullEdgeFalseResidual_injective h,
    Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

theorem singletonFamily_card (k : Nat) :
    (singletonFamily k).card = k := by
  classical
  rw [singletonFamily,
    Finset.card_image_iff.mpr fun i _ j _ h => Finset.singleton_injective h,
    Finset.card_univ, Fintype.card_fin]

end IrrRAFEnumeration
