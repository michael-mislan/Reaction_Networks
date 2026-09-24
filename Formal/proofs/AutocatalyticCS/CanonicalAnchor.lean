import proofs.AutocatalyticCS.ExactSemipositivity
import Mathlib.Data.Finset.Max

/-!
Canonical least-anchor assignment.  This prevents duplicate generation across
ordinary-core anchors before constructing the final output collection.
-/

namespace AutocatalyticCS

variable {A C : Type*} [LinearOrder A] [DecidableEq A]

/-- Least anchor satisfying the concrete containment test.  The proof of
nonemptiness is erased at runtime; ordinary-core anchoring supplies it. -/
def canonicalAnchor (anchors : Finset A) (contains : A → C → Bool) (core : C)
    (hexists : ∃ anchor ∈ anchors, contains anchor core = true) : A :=
  let eligible := anchors.filter fun anchor => contains anchor core
  eligible.min' (by
    rcases hexists with ⟨anchor, hmem, hcontains⟩
    exact ⟨anchor, Finset.mem_filter.2 ⟨hmem, hcontains⟩⟩)

omit [DecidableEq A] in
theorem canonicalAnchor_mem (anchors : Finset A) (contains : A → C → Bool)
    (core : C) (hexists : ∃ anchor ∈ anchors, contains anchor core = true) :
    canonicalAnchor anchors contains core hexists ∈ anchors := by
  have hmem := Finset.min'_mem
    (anchors.filter fun anchor => contains anchor core)
    (by
      rcases hexists with ⟨anchor, hmem, hcontains⟩
      exact ⟨anchor, Finset.mem_filter.2 ⟨hmem, hcontains⟩⟩)
  exact (Finset.mem_filter.1 hmem).1

omit [DecidableEq A] in
theorem canonicalAnchor_contains (anchors : Finset A) (contains : A → C → Bool)
    (core : C) (hexists : ∃ anchor ∈ anchors, contains anchor core = true) :
    contains (canonicalAnchor anchors contains core hexists) core = true := by
  have hmem := Finset.min'_mem
    (anchors.filter fun anchor => contains anchor core)
    (by
      rcases hexists with ⟨anchor, hmem, hcontains⟩
      exact ⟨anchor, Finset.mem_filter.2 ⟨hmem, hcontains⟩⟩)
  exact (Finset.mem_filter.1 hmem).2

omit [DecidableEq A] in
theorem canonicalAnchor_le (anchors : Finset A) (contains : A → C → Bool)
    (core : C) (hexists : ∃ anchor ∈ anchors, contains anchor core = true)
    (anchor : A) (hmem : anchor ∈ anchors) (hcontains : contains anchor core = true) :
    canonicalAnchor anchors contains core hexists ≤ anchor := by
  exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hmem, hcontains⟩)

omit [DecidableEq A] in
theorem existsUnique_canonicalAnchor (anchors : Finset A)
    (contains : A → C → Bool) (core : C)
    (hexists : ∃ anchor ∈ anchors, contains anchor core = true) :
    ∃! anchor, anchor ∈ anchors ∧ contains anchor core = true ∧
      anchor = canonicalAnchor anchors contains core hexists := by
  refine ⟨canonicalAnchor anchors contains core hexists,
    ⟨canonicalAnchor_mem anchors contains core hexists,
      canonicalAnchor_contains anchors contains core hexists, rfl⟩, ?_⟩
  rintro anchor ⟨_, _, hanchor⟩
  exact hanchor

omit [LinearOrder A] [DecidableEq A] in
/-- If each anchor emits only candidates assigned back to it, then outputs of
distinct anchors are disjoint. -/
theorem canonical_emissions_pairwise_disjoint [DecidableEq C]
    (anchorList : List A) (emit : A → List C) (assigned : C → A)
    (hanchors : anchorList.Nodup)
    (hassigned : ∀ anchor core, core ∈ emit anchor → assigned core = anchor) :
    anchorList.Pairwise (Function.onFun List.Disjoint emit) := by
  refine hanchors.imp fun {a b} hab => ?_
  rw [Function.onFun_apply, List.disjoint_left]
  intro core hac hbc
  have ha := hassigned _ _ hac
  have hb := hassigned _ _ hbc
  exact hab (by rw [← ha, ← hb])

omit [LinearOrder A] [DecidableEq A] in
/-- Algorithmic no-duplicates theorem: no final `Finset` deduplication is used.
Local canonical emissions combine into a globally duplicate-free list. -/
theorem nodup_canonical_anchor_flatMap [DecidableEq C]
    (anchorList : List A) (emit : A → List C) (assigned : C → A)
    (hanchors : anchorList.Nodup)
    (hlocal : ∀ anchor ∈ anchorList, (emit anchor).Nodup)
    (hassigned : ∀ anchor core, core ∈ emit anchor → assigned core = anchor) :
    (anchorList.flatMap emit).Nodup := by
  rw [List.nodup_flatMap]
  exact ⟨hlocal,
    canonical_emissions_pairwise_disjoint anchorList emit assigned hanchors hassigned⟩

end AutocatalyticCS
