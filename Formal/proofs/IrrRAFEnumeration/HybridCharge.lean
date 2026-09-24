import proofs.IrrRAFEnumeration.FullCover

namespace IrrRAFEnumeration

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A prospective global charge records a ground vertex, an input edge, and a
displayed blocker member. -/
abbrev RootCharge (α : Type*) := α × (Finset α × Finset α)

def rootCharges (U : Finset α) (F G : Finset (Finset α)) :
    Finset (RootCharge α) :=
  U.product (F.product G)

/-- Root cross-incidences already resolved by leaving the current universe.
At the root itself all cross-incidences are exposed so that the unique root
state can consume one otherwise available charge. -/
def removedCrossCandidates
    (U : Finset α) (F G : Finset (Finset α)) (current : Finset α) :
    Finset (RootCharge α) :=
  (rootCharges U F G).filter fun charge =>
    charge.1 ∈ charge.2.1 ∧ charge.1 ∈ charge.2.2 ∧
      (charge.1 ∉ current ∨ current = U)

theorem removedCrossCandidates_subset_rootCharges
    (U : Finset α) (F G : Finset (Finset α)) (current : Finset α) :
    removedCrossCandidates U F G current ⊆ rootCharges U F G := by
  exact Finset.filter_subset _ _

/-- Polarity-aware root charges for a genuine recursive state.  A removed
vertex distinguishes the two root members, recording which family was
projected and which was filtered at the responsible branch. -/
def removedXorCandidates
    (U : Finset α) (F G : Finset (Finset α)) (current : Finset α) :
    Finset (RootCharge α) :=
  (rootCharges U F G).filter fun charge =>
    charge.1 ∉ current ∧
      ((charge.1 ∈ charge.2.1) ≠ (charge.1 ∈ charge.2.2))

/-- The charges exposed by one recursion edge, rather than by the entire path
from the root.  This is the local relation needed by a recursive Hall proof. -/
def entryRemovedXorCandidates
    (U : Finset α) (F G : Finset (Finset α))
    (parent current : Finset α) : Finset (RootCharge α) :=
  (rootCharges U F G).filter fun charge =>
    charge.1 ∈ parent ∧ charge.1 ∉ current ∧
      ((charge.1 ∈ charge.2.1) ≠ (charge.1 ∈ charge.2.2))

/-- Reconstructive charges for genuine hybrid entries.  Besides crossing a
newly removed vertex, the common trace of the root edge/output pair must still
be present in the child universe.  Factor entries need separate accounting. -/
def entrySurvivorXorCandidates
    (U : Finset α) (F G : Finset (Finset α))
    (parent current : Finset α) : Finset (RootCharge α) :=
  (entryRemovedXorCandidates U F G parent current).filter fun charge =>
    charge.2.1 ∩ charge.2.2 ⊆ current

/-- Two singleton-deletion pivot entries can share a survivor charge only when
they delete the same vertex.  The first coordinate of the common root charge
lies in each parent and outside the corresponding erased child, so it is both
deleted vertices. -/
theorem pivot_entrySurvivorXorCandidates_overlap_imp_eq
    (U : Finset α) (F G : Finset (Finset α))
    (parent₁ parent₂ : Finset α) (x y : α)
    (hOverlap :
      (entrySurvivorXorCandidates U F G parent₁ (parent₁.erase x) ∩
        entrySurvivorXorCandidates U F G parent₂ (parent₂.erase y)).Nonempty) :
    x = y := by
  obtain ⟨charge, hcharge⟩ := hOverlap
  obtain ⟨hcharge₁, hcharge₂⟩ := Finset.mem_inter.mp hcharge
  obtain ⟨hentry₁, _hsurvive₁⟩ := Finset.mem_filter.mp hcharge₁
  obtain ⟨_hroot₁, hparent₁, herase₁, _hxor₁⟩ :=
    Finset.mem_filter.mp hentry₁
  obtain ⟨hentry₂, _hsurvive₂⟩ := Finset.mem_filter.mp hcharge₂
  obtain ⟨_hroot₂, hparent₂, herase₂, _hxor₂⟩ :=
    Finset.mem_filter.mp hentry₂
  have hchargeX : charge.1 = x := by
    by_contra hne
    exact herase₁ (Finset.mem_erase.mpr ⟨hne, hparent₁⟩)
  have hchargeY : charge.1 = y := by
    by_contra hne
    exact herase₂ (Finset.mem_erase.mpr ⟨hne, hparent₂⟩)
  exact hchargeX.symm.trans hchargeY

/-- Displayed outputs through `x` whose intersection with a fixed root input
edge survives in the child universe.  For a pivot with `x ∉ E`, every member
of this fiber supplies a distinct survivor charge. -/
def survivorOutputFiber
    (G : Finset (Finset α)) (current : Finset α) (x : α) (E : Finset α) :
    Finset (Finset α) :=
  G.filter fun D => x ∈ D ∧ E ∩ D ⊆ current

/-- Symmetric input-edge fiber for a fixed displayed output omitting `x`. -/
def survivorInputFiber
    (F : Finset (Finset α)) (current : Finset α) (x : α) (D : Finset α) :
    Finset (Finset α) :=
  F.filter fun E => x ∈ E ∧ E ∩ D ⊆ current

/-- A surviving output fiber injects into the pivot child's root-charge
neighborhood.  This is the exact bridge from an opposite-family frequency
lower bound to a survivor-candidate degree lower bound. -/
theorem survivorOutputFiber_card_le_entrySurvivorXorCandidates
    (U : Finset α) (F G : Finset (Finset α))
    (parent current E : Finset α) (x : α)
    (hParentU : parent ⊆ U) (hEF : E ∈ F)
    (hxParent : x ∈ parent) (hxCurrent : x ∉ current)
    (hxE : x ∉ E) :
    (survivorOutputFiber G current x E).card ≤
      (entrySurvivorXorCandidates U F G parent current).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun D => (x, (E, D)))
  · intro D hD
    obtain ⟨hDG, hxD, hsurvive⟩ := Finset.mem_filter.mp hD
    simp [entrySurvivorXorCandidates, entryRemovedXorCandidates,
      rootCharges, hParentU hxParent, hEF, hDG, hxParent, hxCurrent,
      hxE, hxD, hsurvive]
  · intro D₁ _hD₁ D₂ _hD₂ hEq
    exact Prod.mk.inj (Prod.mk.inj hEq).2 |>.2

/-- The polarity-reversed surviving input fiber gives the symmetric degree
lower bound. -/
theorem survivorInputFiber_card_le_entrySurvivorXorCandidates
    (U : Finset α) (F G : Finset (Finset α))
    (parent current D : Finset α) (x : α)
    (hParentU : parent ⊆ U) (hDG : D ∈ G)
    (hxParent : x ∈ parent) (hxCurrent : x ∉ current)
    (hxD : x ∉ D) :
    (survivorInputFiber F current x D).card ≤
      (entrySurvivorXorCandidates U F G parent current).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun E => (x, (E, D)))
  · intro E hE
    obtain ⟨hEF, hxE, hsurvive⟩ := Finset.mem_filter.mp hE
    simp [entrySurvivorXorCandidates, entryRemovedXorCandidates,
      rootCharges, hParentU hxParent, hEF, hDG, hxParent, hxCurrent,
      hxE, hxD, hsurvive]
  · intro E₁ _hE₁ E₂ _hE₂ hEq
    exact Prod.mk.inj (Prod.mk.inj hEq).2 |>.1

/-- When both polarities retain a root member omitting the pivot, their two
surviving frequent fibers give disjoint blocks of charges.  Thus their
cardinalities add, rather than merely taking the larger of the two one-sided
bounds. -/
theorem survivorFibers_add_card_le_entrySurvivorXorCandidates
    (U : Finset α) (F G : Finset (Finset α))
    (parent current E D : Finset α) (x : α)
    (hParentU : parent ⊆ U) (hEF : E ∈ F) (hDG : D ∈ G)
    (hxParent : x ∈ parent) (hxCurrent : x ∉ current)
    (hxE : x ∉ E) (hxD : x ∉ D) :
    (survivorOutputFiber G current x E).card +
        (survivorInputFiber F current x D).card ≤
      (entrySurvivorXorCandidates U F G parent current).card := by
  classical
  let outputCharges :=
    (survivorOutputFiber G current x E).image fun D' => (x, (E, D'))
  let inputCharges :=
    (survivorInputFiber F current x D).image fun E' => (x, (E', D))
  have hOutputCard : outputCharges.card =
      (survivorOutputFiber G current x E).card := by
    apply Finset.card_image_iff.mpr
    intro D₁ _hD₁ D₂ _hD₂ hEq
    exact Prod.mk.inj (Prod.mk.inj hEq).2 |>.2
  have hInputCard : inputCharges.card =
      (survivorInputFiber F current x D).card := by
    apply Finset.card_image_iff.mpr
    intro E₁ _hE₁ E₂ _hE₂ hEq
    exact Prod.mk.inj (Prod.mk.inj hEq).2 |>.1
  have hDisjoint : Disjoint outputCharges inputCharges := by
    rw [Finset.disjoint_left]
    intro charge hOutput hInput
    obtain ⟨D', hD', rfl⟩ := Finset.mem_image.mp hOutput
    obtain ⟨E', hE', hEq⟩ := Finset.mem_image.mp hInput
    have hD'eq : D' = D := Prod.mk.inj (Prod.mk.inj hEq).2 |>.2.symm
    have hxD' : x ∈ D' := (Finset.mem_filter.mp hD').2.1
    exact hxD (hD'eq ▸ hxD')
  have hUnion : outputCharges ∪ inputCharges ⊆
      entrySurvivorXorCandidates U F G parent current := by
    intro charge hcharge
    rcases Finset.mem_union.mp hcharge with hOutput | hInput
    · obtain ⟨D', hD', rfl⟩ := Finset.mem_image.mp hOutput
      obtain ⟨hD'G, hxD', hsurvive⟩ := Finset.mem_filter.mp hD'
      simp [entrySurvivorXorCandidates, entryRemovedXorCandidates,
        rootCharges, hParentU hxParent, hEF, hD'G, hxParent, hxCurrent,
        hxE, hxD', hsurvive]
    · obtain ⟨E', hE', rfl⟩ := Finset.mem_image.mp hInput
      obtain ⟨hE'F, hxE', hsurvive⟩ := Finset.mem_filter.mp hE'
      simp [entrySurvivorXorCandidates, entryRemovedXorCandidates,
        rootCharges, hParentU hxParent, hE'F, hDG, hxParent, hxCurrent,
        hxE', hxD, hsurvive]
  rw [← hOutputCard, ← hInputCard,
    ← Finset.card_union_of_disjoint hDisjoint]
  exact Finset.card_le_card hUnion

/-- At a pivot deleting `x`, every root member already filtered inside the
parent and containing `x` belongs to the corresponding survivor fiber, as
soon as the fixed opposite-polarity witness omits `x`. -/
theorem filteredVertexFibers_add_card_le_entrySurvivorXorCandidates
    (U : Finset α) (F G : Finset (Finset α))
    (parent E D : Finset α) (x : α)
    (hParentU : parent ⊆ U) (hEF : E ∈ F) (hDG : D ∈ G)
    (hxParent : x ∈ parent) (hxE : x ∉ E) (hxD : x ∉ D) :
    ((filterWithin G parent).filter fun D' => x ∈ D').card +
        ((filterWithin F parent).filter fun E' => x ∈ E').card ≤
      (entrySurvivorXorCandidates U F G parent (parent.erase x)).card := by
  classical
  have hOutput :
      (filterWithin G parent).filter (fun D' => x ∈ D') ⊆
        survivorOutputFiber G (parent.erase x) x E := by
    intro D' hD'
    obtain ⟨hD'Filtered, hxD'⟩ := Finset.mem_filter.mp hD'
    obtain ⟨hD'G, hD'Parent⟩ := Finset.mem_filter.mp hD'Filtered
    apply Finset.mem_filter.mpr
    refine ⟨hD'G, hxD', ?_⟩
    intro y hy
    obtain ⟨hyE, hyD'⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_erase.mpr ⟨fun hyx => hxE (hyx ▸ hyE), hD'Parent hyD'⟩
  have hInput :
      (filterWithin F parent).filter (fun E' => x ∈ E') ⊆
        survivorInputFiber F (parent.erase x) x D := by
    intro E' hE'
    obtain ⟨hE'Filtered, hxE'⟩ := Finset.mem_filter.mp hE'
    obtain ⟨hE'F, hE'Parent⟩ := Finset.mem_filter.mp hE'Filtered
    apply Finset.mem_filter.mpr
    refine ⟨hE'F, hxE', ?_⟩
    intro y hy
    obtain ⟨hyE', hyD⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_erase.mpr ⟨fun hyx => hxD (hyx ▸ hyD), hE'Parent hyE'⟩
  exact (Nat.add_le_add (Finset.card_le_card hOutput)
    (Finset.card_le_card hInput)).trans
      (survivorFibers_add_card_le_entrySurvivorXorCandidates
        U F G parent (parent.erase x) E D x hParentU hEF hDG hxParent
        (by simp) hxE hxD)

/-- Strictly non-universal pivot fibers automatically supply the two omitted
root witnesses required by the additive survivor-fiber bound.  This packages
the exact `frequency < 1` side condition of a genuine two-sided pivot. -/
theorem filteredVertexFibers_add_card_le_of_proper
    (U : Finset α) (F G : Finset (Finset α))
    (parent : Finset α) (x : α)
    (hParentU : parent ⊆ U) (hxParent : x ∈ parent)
    (hProperF :
      ((filterWithin F parent).filter fun E => x ∈ E).card <
        (filterWithin F parent).card)
    (hProperG :
      ((filterWithin G parent).filter fun D => x ∈ D).card <
        (filterWithin G parent).card) :
    ((filterWithin G parent).filter fun D => x ∈ D).card +
        ((filterWithin F parent).filter fun E => x ∈ E).card ≤
      (entrySurvivorXorCandidates U F G parent (parent.erase x)).card := by
  classical
  have hExistF : ∃ E ∈ filterWithin F parent, x ∉ E := by
    by_contra hNone
    push Not at hNone
    have hEq : ((filterWithin F parent).filter fun E => x ∈ E) =
        filterWithin F parent := by
      ext E
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hE
        exact ⟨hE, hNone E hE⟩
    rw [hEq] at hProperF
    exact (Nat.lt_irrefl _) hProperF
  have hExistG : ∃ D ∈ filterWithin G parent, x ∉ D := by
    by_contra hNone
    push Not at hNone
    have hEq : ((filterWithin G parent).filter fun D => x ∈ D) =
        filterWithin G parent := by
      ext D
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hD
        exact ⟨hD, hNone D hD⟩
    rw [hEq] at hProperG
    exact (Nat.lt_irrefl _) hProperG
  obtain ⟨E, hEFiltered, hxE⟩ := hExistF
  obtain ⟨D, hDFiltered, hxD⟩ := hExistG
  have hEF : E ∈ F := (Finset.mem_filter.mp hEFiltered).1
  have hDG : D ∈ G := (Finset.mem_filter.mp hDFiltered).1
  exact filteredVertexFibers_add_card_le_entrySurvivorXorCandidates
    U F G parent E D x hParentU hEF hDG hxParent hxE hxD

/-- One-sided version for a universal/proper pivot: properness of the input
fiber supplies an input witness omitting `x`, so the entire filtered output
fiber through `x` injects into survivor charges. -/
theorem filteredOutputVertexFiber_card_le_of_inputProper
    (U : Finset α) (F G : Finset (Finset α))
    (parent : Finset α) (x : α)
    (hParentU : parent ⊆ U) (hxParent : x ∈ parent)
    (hProperF :
      ((filterWithin F parent).filter fun E => x ∈ E).card <
        (filterWithin F parent).card) :
    ((filterWithin G parent).filter fun D => x ∈ D).card ≤
      (entrySurvivorXorCandidates U F G parent (parent.erase x)).card := by
  classical
  have hExistF : ∃ E ∈ filterWithin F parent, x ∉ E := by
    by_contra hNone
    push Not at hNone
    have hEq : ((filterWithin F parent).filter fun E => x ∈ E) =
        filterWithin F parent := by
      ext E
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hE
        exact ⟨hE, hNone E hE⟩
    rw [hEq] at hProperF
    exact (Nat.lt_irrefl _) hProperF
  obtain ⟨E, hEFiltered, hxE⟩ := hExistF
  have hEF : E ∈ F := (Finset.mem_filter.mp hEFiltered).1
  have hSub : (filterWithin G parent).filter (fun D => x ∈ D) ⊆
      survivorOutputFiber G (parent.erase x) x E := by
    intro D hD
    obtain ⟨hDFiltered, hxD⟩ := Finset.mem_filter.mp hD
    obtain ⟨hDG, hDParent⟩ := Finset.mem_filter.mp hDFiltered
    apply Finset.mem_filter.mpr
    refine ⟨hDG, hxD, ?_⟩
    intro y hy
    obtain ⟨hyE, hyD⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_erase.mpr ⟨fun hyx => hxE (hyx ▸ hyE), hDParent hyD⟩
  exact (Finset.card_le_card hSub).trans
    (survivorOutputFiber_card_le_entrySurvivorXorCandidates
      U F G parent (parent.erase x) E x hParentU hEF hxParent
      (by simp) hxE)

/-- Symmetric one-sided pivot bound. -/
theorem filteredInputVertexFiber_card_le_of_outputProper
    (U : Finset α) (F G : Finset (Finset α))
    (parent : Finset α) (x : α)
    (hParentU : parent ⊆ U) (hxParent : x ∈ parent)
    (hProperG :
      ((filterWithin G parent).filter fun D => x ∈ D).card <
        (filterWithin G parent).card) :
    ((filterWithin F parent).filter fun E => x ∈ E).card ≤
      (entrySurvivorXorCandidates U F G parent (parent.erase x)).card := by
  classical
  have hExistG : ∃ D ∈ filterWithin G parent, x ∉ D := by
    by_contra hNone
    push Not at hNone
    have hEq : ((filterWithin G parent).filter fun D => x ∈ D) =
        filterWithin G parent := by
      ext D
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hD
        exact ⟨hD, hNone D hD⟩
    rw [hEq] at hProperG
    exact (Nat.lt_irrefl _) hProperG
  obtain ⟨D, hDFiltered, hxD⟩ := hExistG
  have hDG : D ∈ G := (Finset.mem_filter.mp hDFiltered).1
  have hSub : (filterWithin F parent).filter (fun E => x ∈ E) ⊆
      survivorInputFiber F (parent.erase x) x D := by
    intro E hE
    obtain ⟨hEFiltered, hxE⟩ := Finset.mem_filter.mp hE
    obtain ⟨hEF, hEParent⟩ := Finset.mem_filter.mp hEFiltered
    apply Finset.mem_filter.mpr
    refine ⟨hEF, hxE, ?_⟩
    intro y hy
    obtain ⟨hyE, hyD⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_erase.mpr ⟨fun hyx => hxD (hyx ▸ hyD), hEParent hyE⟩
  exact (Finset.card_le_card hSub).trans
    (survivorInputFiber_card_le_entrySurvivorXorCandidates
      U F G parent (parent.erase x) D x hParentU hDG hxParent
      (by simp) hxD)

/-- Complete local pivot case split.  If at least one side is proper, both
pivot fibers are nonempty, and any universal side has at least two members,
then the common pivot neighborhood contains at least two survivor charges—one
for each possible child of the binary pivot. -/
theorem two_le_entrySurvivorXorCandidates_of_pivotFibers
    (U : Finset α) (F G : Finset (Finset α))
    (parent : Finset α) (x : α)
    (hParentU : parent ⊆ U) (hxParent : x ∈ parent)
    (hSomeProper :
      ((filterWithin F parent).filter fun E => x ∈ E).card <
          (filterWithin F parent).card ∨
        ((filterWithin G parent).filter fun D => x ∈ D).card <
          (filterWithin G parent).card)
    (hPositiveF :
      0 < ((filterWithin F parent).filter fun E => x ∈ E).card)
    (hPositiveG :
      0 < ((filterWithin G parent).filter fun D => x ∈ D).card)
    (hUniversalF :
      ¬ ((filterWithin F parent).filter fun E => x ∈ E).card <
          (filterWithin F parent).card →
        2 ≤ ((filterWithin F parent).filter fun E => x ∈ E).card)
    (hUniversalG :
      ¬ ((filterWithin G parent).filter fun D => x ∈ D).card <
          (filterWithin G parent).card →
        2 ≤ ((filterWithin G parent).filter fun D => x ∈ D).card) :
    2 ≤ (entrySurvivorXorCandidates U F G parent
      (parent.erase x)).card := by
  by_cases hProperF :
      ((filterWithin F parent).filter fun E => x ∈ E).card <
        (filterWithin F parent).card
  · by_cases hProperG :
        ((filterWithin G parent).filter fun D => x ∈ D).card <
          (filterWithin G parent).card
    · have hBound := filteredVertexFibers_add_card_le_of_proper
        U F G parent x hParentU hxParent hProperF hProperG
      have hTwo : 2 ≤
          ((filterWithin G parent).filter fun D => x ∈ D).card +
            ((filterWithin F parent).filter fun E => x ∈ E).card := by
        omega
      exact hTwo.trans hBound
    · exact (hUniversalG hProperG).trans
        (filteredOutputVertexFiber_card_le_of_inputProper
          U F G parent x hParentU hxParent hProperF)
  · have hProperG := hSomeProper.resolve_left hProperF
    exact (hUniversalF hProperF).trans
      (filteredInputVertexFiber_card_le_of_outputProper
        U F G parent x hParentU hxParent hProperG)

/-- All root XOR charges whose distinguished vertex lies in `X`. -/
def xorChargesWithin
    (U : Finset α) (F G : Finset (Finset α)) (X : Finset α) :
    Finset (RootCharge α) :=
  (rootCharges U F G).filter fun charge =>
    charge.1 ∈ X ∧
      ((charge.1 ∈ charge.2.1) ≠ (charge.1 ∈ charge.2.2))

/-- States whose entire first-entry removal is supported inside `X`. -/
def entrySupportedWithin
    (states : Finset β) (parent current : β → Finset α) (X : Finset α) :
    Finset β :=
  states.filter fun state => parent state \ current state ⊆ X

theorem removedXorCandidates_subset_rootCharges
    (U : Finset α) (F G : Finset (Finset α)) (current : Finset α) :
    removedXorCandidates U F G current ⊆ rootCharges U F G := by
  exact Finset.filter_subset _ _

theorem entryRemovedXorCandidates_subset_removedXorCandidates
    (U : Finset α) (F G : Finset (Finset α))
    (parent current : Finset α) :
    entryRemovedXorCandidates U F G parent current ⊆
      removedXorCandidates U F G current := by
  intro charge hcharge
  simp only [entryRemovedXorCandidates, removedXorCandidates,
    Finset.mem_filter] at hcharge ⊢
  exact ⟨hcharge.1, hcharge.2.2.1, hcharge.2.2.2⟩

theorem entrySurvivorXorCandidates_subset_entryRemovedXorCandidates
    (U : Finset α) (F G : Finset (Finset α))
    (parent current : Finset α) :
    entrySurvivorXorCandidates U F G parent current ⊆
      entryRemovedXorCandidates U F G parent current := by
  exact Finset.filter_subset _ _

/-- Hall expansion of a family of states into their admissible root charges. -/
def HasChargeExpansion
    (states : Finset β) (candidates : β → Finset (RootCharge α)) : Prop :=
  ∀ sub ⊆ states, sub.card ≤ (sub.biUnion candidates).card

omit [DecidableEq β] in
theorem HasChargeExpansion.monoCandidates
    {states : Finset β}
    {small large : β → Finset (RootCharge α)}
    (hExpansion : HasChargeExpansion states small)
    (hmono : ∀ state ∈ states, small state ⊆ large state) :
    HasChargeExpansion states large := by
  intro sub hsub
  calc
    sub.card ≤ (sub.biUnion small).card := hExpansion sub hsub
    _ ≤ (sub.biUnion large).card := by
      apply Finset.card_le_card
      intro charge hcharge
      obtain ⟨state, hstate, hchargeSmall⟩ :=
        Finset.mem_biUnion.mp hcharge
      exact Finset.mem_biUnion.mpr
        ⟨state, hstate, hmono state (hsub hstate) hchargeSmall⟩

omit [DecidableEq β] in
theorem biUnion_entryRemovedXorCandidates
    (U : Finset α) (F G : Finset (Finset α))
    (sub : Finset β) (parent current : β → Finset α) :
    (sub.biUnion fun state =>
      entryRemovedXorCandidates U F G (parent state) (current state)) =
      xorChargesWithin U F G
        (sub.biUnion fun state => parent state \ current state) := by
  ext charge
  simp only [Finset.mem_biUnion, entryRemovedXorCandidates,
    xorChargesWithin, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨state, hstate, hroot, hparent, hcurrent, hxor⟩
    exact ⟨hroot, ⟨⟨state, hstate, hparent, hcurrent⟩, hxor⟩⟩
  · rintro ⟨hroot, ⟨⟨state, hstate, hparent, hcurrent⟩, hxor⟩⟩
    exact ⟨state, hstate, hroot, hparent, hcurrent, hxor⟩

omit [DecidableEq β] in
/-- Hall's condition for first-entry candidates follows from its equivalent
vertex-cut form.  This is the induction-ready statement: a cut `X` must pay
for every state whose newly removed vertices are all contained in `X`. -/
theorem hasChargeExpansion_of_entryCutBounds
    (U : Finset α) (F G : Finset (Finset α))
    (states : Finset β) (parent current : β → Finset α)
    (hCut : ∀ X,
      (entrySupportedWithin states parent current X).card ≤
        (xorChargesWithin U F G X).card) :
    HasChargeExpansion states fun state =>
      entryRemovedXorCandidates U F G (parent state) (current state) := by
  intro sub hsub
  let X := sub.biUnion fun state => parent state \ current state
  calc
    sub.card ≤ (entrySupportedWithin states parent current X).card := by
      apply Finset.card_le_card
      intro state hstate
      apply Finset.mem_filter.mpr
      refine ⟨hsub hstate, ?_⟩
      intro vertex hvertex
      exact Finset.mem_biUnion.mpr ⟨state, hstate, hvertex⟩
    _ ≤ (xorChargesWithin U F G X).card := hCut X
    _ = (sub.biUnion fun state =>
        entryRemovedXorCandidates U F G
          (parent state) (current state)).card := by
      rw [biUnion_entryRemovedXorCandidates]

omit [DecidableEq α] in
theorem rootCharges_card (U : Finset α) (F G : Finset (Finset α)) :
    (rootCharges U F G).card = U.card * F.card * G.card := by
  simp [rootCharges, Nat.mul_assoc]

omit [DecidableEq β] in
/-- Exact quantitative adapter for the live hybrid route.  Once every
subfamily of reached states expands into at least as many compatible root
triples, the total number of states is polynomial in the displayed dual pair. -/
theorem states_card_le_rootChargeBudget
    (U : Finset α) (F G : Finset (Finset α))
    (states : Finset β) (candidates : β → Finset (RootCharge α))
    (hCandidates : ∀ s ∈ states, candidates s ⊆ rootCharges U F G)
    (hExpansion : HasChargeExpansion states candidates) :
    states.card ≤ U.card * F.card * G.card := by
  calc
    states.card ≤ (states.biUnion candidates).card :=
      hExpansion states Finset.Subset.rfl
    _ ≤ (rootCharges U F G).card := by
      apply Finset.card_le_card
      intro charge hcharge
      obtain ⟨state, hstate, hchargeState⟩ :=
        Finset.mem_biUnion.mp hcharge
      exact hCandidates state hstate hchargeState
    _ = U.card * F.card * G.card := rootCharges_card U F G

omit [DecidableEq β] in
/-- The exact quantitative consequence of the live global-charge conjecture.
It remains to prove Hall expansion for the reached hybrid states; no separate
universe-counting hypothesis is used here. -/
theorem states_card_le_of_removedCrossExpansion
    (U : Finset α) (F G : Finset (Finset α))
    (states : Finset β) (current : β → Finset α)
    (hExpansion :
      HasChargeExpansion states fun s =>
        removedCrossCandidates U F G (current s)) :
    states.card ≤ U.card * F.card * G.card := by
  apply states_card_le_rootChargeBudget U F G states
    (fun s => removedCrossCandidates U F G (current s))
  · intro s _hs
    exact removedCrossCandidates_subset_rootCharges U F G (current s)
  · exact hExpansion

omit [DecidableEq β] in
/-- The polarity-aware Hall premise bounds all nonroot states by the root
triple budget. -/
theorem states_card_le_of_removedXorExpansion
    (U : Finset α) (F G : Finset (Finset α))
    (states : Finset β) (current : β → Finset α)
    (hExpansion :
      HasChargeExpansion states fun s =>
        removedXorCandidates U F G (current s)) :
    states.card ≤ U.card * F.card * G.card := by
  apply states_card_le_rootChargeBudget U F G states
    (fun s => removedXorCandidates U F G (current s))
  · intro s _hs
    exact removedXorCandidates_subset_rootCharges U F G (current s)
  · exact hExpansion

omit [DecidableEq β] in
/-- Exact accounting of the unique root state.  Once the nonroot states have
polarity-aware Hall expansion, the entire memo DAG has size at most
`1 + |U| |F| |G|`. -/
theorem states_card_le_one_add_of_removedXorExpansion
    (U : Finset α) (F G : Finset (Finset α))
    (states : Finset β) (current : β → Finset α)
    (hRootFiber : (states.filter fun s => current s = U).card ≤ 1)
    (hExpansion :
      HasChargeExpansion (states.filter fun s => current s ≠ U) fun s =>
        removedXorCandidates U F G (current s)) :
    states.card ≤ 1 + U.card * F.card * G.card := by
  classical
  have hNonroot :
      (states.filter fun s => current s ≠ U).card ≤
        U.card * F.card * G.card :=
    states_card_le_of_removedXorExpansion U F G
      (states.filter fun s => current s ≠ U) current hExpansion
  have hPartition :
      (states.filter fun s => current s = U).card +
          (states.filter fun s => current s ≠ U).card = states.card :=
    by
      simpa only [ne_eq] using
        (Finset.card_filter_add_card_filter_not
          (s := states) (p := fun s => current s = U))
  calc
    states.card =
        (states.filter fun s => current s = U).card +
          (states.filter fun s => current s ≠ U).card := hPartition.symm
    _ ≤ 1 + U.card * F.card * G.card :=
      Nat.add_le_add hRootFiber hNonroot

omit [DecidableEq β] in
/-- An induction may expose charges only at the edge by which each state is
first entered.  Hall expansion for those smaller neighborhoods already implies
the global polynomial memo-state bound. -/
theorem states_card_le_one_add_of_entryRemovedXorExpansion
    (U : Finset α) (F G : Finset (Finset α))
    (states : Finset β) (parent current : β → Finset α)
    (hRootFiber : (states.filter fun s => current s = U).card ≤ 1)
    (hExpansion :
      HasChargeExpansion (states.filter fun s => current s ≠ U) fun s =>
        entryRemovedXorCandidates U F G (parent s) (current s)) :
    states.card ≤ 1 + U.card * F.card * G.card := by
  apply states_card_le_one_add_of_removedXorExpansion
    U F G states current hRootFiber
  exact hExpansion.monoCandidates fun state _hstate =>
    entryRemovedXorCandidates_subset_removedXorCandidates
      U F G (parent state) (current state)

omit [DecidableEq β] in
/-- The cut form is sufficient for the complete memo-state bound.  Thus the
remaining combinatorial obligation can be stated without quantifying over
subfamilies of states: every vertex cut must contain enough root XOR charges
to pay for the nonroot states whose first-entry removals lie in that cut. -/
theorem states_card_le_one_add_of_entryCutBounds
    (U : Finset α) (F G : Finset (Finset α))
    (states : Finset β) (parent current : β → Finset α)
    (hRootFiber : (states.filter fun s => current s = U).card ≤ 1)
    (hCut : ∀ X,
      (entrySupportedWithin
        (states.filter fun s => current s ≠ U) parent current X).card ≤
        (xorChargesWithin U F G X).card) :
    states.card ≤ 1 + U.card * F.card * G.card := by
  apply states_card_le_one_add_of_entryRemovedXorExpansion
    U F G states parent current hRootFiber
  exact hasChargeExpansion_of_entryCutBounds U F G
    (states.filter fun s => current s ≠ U) parent current hCut

omit [DecidableEq β] in
/-- Survivor-compatible Hall expansion already bounds all genuine hybrid-entry
states by the root triple budget.  Component-factor nodes are deliberately not
included: they are to be paid by the separate factor-forest argument. -/
theorem hybridStates_card_le_of_entrySurvivorExpansion
    (U : Finset α) (F G : Finset (Finset α))
    (hybridStates : Finset β) (parent current : β → Finset α)
    (hExpansion :
      HasChargeExpansion hybridStates fun s =>
        entrySurvivorXorCandidates U F G (parent s) (current s)) :
    hybridStates.card ≤ U.card * F.card * G.card := by
  apply states_card_le_rootChargeBudget U F G hybridStates
    (fun s => entrySurvivorXorCandidates U F G (parent s) (current s))
  · intro state _hstate charge hcharge
    exact entryRemovedXorCandidates_subset_removedXorCandidates
      U F G (parent state) (current state)
      (entrySurvivorXorCandidates_subset_entryRemovedXorCandidates
        U F G (parent state) (current state) hcharge)
      |> removedXorCandidates_subset_rootCharges U F G (current state)
  · exact hExpansion

end IrrRAFEnumeration
