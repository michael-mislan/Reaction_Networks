import Mathlib

namespace RAFStructuredEnumeration
variable {R : Type*}

def DependencyClosed (d : R → Finset R) (S : Finset R) : Prop :=
  ∀ r ∈ S, d r ⊆ S

def Reaches (d : R → Finset R) : R → R → Prop :=
  Relation.ReflTransGen (fun r s => s ∈ d r)

noncomputable def reachable (K : Finset R) (d : R → Finset R) (r : R) : Finset R := by
  classical
  exact K.filter (Reaches d r)

@[simp] theorem mem_reachable (K : Finset R) (d : R → Finset R) (r s : R) :
    s ∈ reachable K d r ↔ s ∈ K ∧ Reaches d r s := by
  classical
  simp [reachable]

theorem closed_reaches (d : R → Finset R) (S : Finset R)
    (hc : DependencyClosed d S) {r s : R} (hr : r ∈ S) (h : Reaches d r s) :
    s ∈ S := by
  induction h with
  | refl => exact hr
  | tail _ hstep ih => exact hc _ ih hstep

theorem reachable_closed (K : Finset R) (d : R → Finset R)
    (hK : DependencyClosed d K) (r : R) : DependencyClosed d (reachable K d r) := by
  intro s hs t ht
  obtain ⟨hsK, hrs⟩ := (mem_reachable K d r s).mp hs
  exact (mem_reachable K d r t).mpr ⟨hK s hsK ht, hrs.tail ht⟩

noncomputable def sinkCandidates (K : Finset R) (d : R → Finset R) :
    Finset (Finset R) := by
  classical
  exact (K.filter (fun r => ∀ s ∈ reachable K d r, Reaches d s r)).image (reachable K d)

theorem sinkCandidates_card (K : Finset R) (d : R → Finset R) :
    (sinkCandidates K d).card ≤ K.card := by
  classical
  exact (Finset.card_image_le).trans (Finset.card_filter_le _ _)

/-- Sink SCCs include isolated singleton vertices. The direction of each arc is
consumer to supplier. No enumeration of vertex subsets is used by this family. -/
theorem minimal_closed_iff_sink (K : Finset R) (d : R → Finset R)
    (hK : DependencyClosed d K) (S : Finset R) (hSK : S ⊆ K) :
    (S.Nonempty ∧ DependencyClosed d S ∧
      ∀ T, T.Nonempty → DependencyClosed d T → T ⊆ S → S ⊆ T) ↔
      S ∈ sinkCandidates K d := by
  classical
  constructor
  · rintro ⟨hn, hc, hm⟩
    obtain ⟨r, hr⟩ := hn
    have hreachsub : reachable K d r ⊆ S := by
      intro s hs
      exact closed_reaches d S hc hr ((mem_reachable K d r s).mp hs).2
    have hrreach : r ∈ reachable K d r :=
      (mem_reachable K d r r).mpr ⟨hSK hr, .refl⟩
    have heq : reachable K d r = S := Finset.Subset.antisymm hreachsub
      (hm _ ⟨r, hrreach⟩ (reachable_closed K d hK r) hreachsub)
    apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_filter.mpr ⟨hSK hr, ?_⟩, heq⟩
    intro s hs
    have hsS : s ∈ S := hreachsub hs
    have hss : s ∈ reachable K d s :=
      (mem_reachable K d s s).mpr ⟨hSK hsS, .refl⟩
    have hsub : reachable K d s ⊆ S := by
      intro t ht
      exact closed_reaches d S hc hsS ((mem_reachable K d s t).mp ht).2
    have hrin := hm _ ⟨s, hss⟩ (reachable_closed K d hK s) hsub hr
    exact ((mem_reachable K d s r).mp hrin).2
  · intro hsink
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hsink
    obtain ⟨hrK, hreturn⟩ := Finset.mem_filter.mp hr
    subst S
    refine ⟨⟨r, (mem_reachable K d r r).mpr ⟨hrK, .refl⟩⟩,
      reachable_closed K d hK r, ?_⟩
    intro T hn hc hT
    obtain ⟨s, hs⟩ := hn
    have hrT : r ∈ T := closed_reaches d T hc hs (hreturn s (hT hs))
    intro t ht
    exact closed_reaches d T hc hrT ((mem_reachable K d r t).mp ht).2

end RAFStructuredEnumeration
