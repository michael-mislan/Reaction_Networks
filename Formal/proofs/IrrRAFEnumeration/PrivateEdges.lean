import proofs.IrrRAFEnumeration.FiniteDuality

namespace IrrRAFEnumeration

variable {α : Type*} [DecidableEq α]

/-- Every element of a minimal transversal has a private input edge: an edge
whose intersection with the transversal is exactly that element.  This is the
extra promise distinguishing valid completion CNFs from arbitrary
cross-intersecting clause pairs. -/
theorem minimal_hitter_private_edge
    {H : Finset (Finset α)} {T : Finset α}
    (hT : Minimal (Hits H) T) {x : α} (hxT : x ∈ T) :
    ∃ E ∈ H, T ∩ E = {x} := by
  classical
  have hnot : ¬ Hits H (T.erase x) := by
    intro herase
    have hsub : T ⊆ T.erase x := hT.2 herase (Finset.erase_subset x T)
    have hxErase : x ∈ T.erase x := hsub hxT
    simp at hxErase
  simp only [Hits, not_forall, not_not] at hnot
  obtain ⟨E, hE, hdisjoint⟩ := hnot
  have hinterSub : T ∩ E ⊆ {x} := by
    intro y hy
    have hyT : y ∈ T := (Finset.mem_inter.mp hy).1
    have hyE : y ∈ E := (Finset.mem_inter.mp hy).2
    by_contra hyx
    have hyne : y ≠ x := by simpa using hyx
    have hyErase : y ∈ T.erase x := Finset.mem_erase.mpr ⟨hyne, hyT⟩
    exact (Finset.disjoint_left.mp hdisjoint) hyErase hyE
  have hTE : ¬ Disjoint T E := hT.1 E hE
  obtain ⟨y, hyT, hyE⟩ := Finset.not_disjoint_iff.mp hTE
  have hyInter : y ∈ T ∩ E := Finset.mem_inter.mpr ⟨hyT, hyE⟩
  have hyx : y = x := Finset.mem_singleton.mp (hinterSub hyInter)
  exact ⟨E, hE, Finset.Subset.antisymm hinterSub
    (Finset.singleton_subset_iff.mpr (hyx ▸ hyInter))⟩

theorem blocker_private_edge
    [Fintype α]
    {H : Finset (Finset α)} {T : Finset α}
    (hT : T ∈ blocker H) {x : α} (hxT : x ∈ T) :
    ∃ E ∈ H, T ∩ E = {x} :=
  minimal_hitter_private_edge (mem_blocker.mp hT) hxT

/-- Private-edge branching is complete.  If a hitting set `S` avoids a known
minimal transversal `T`, then it omits some `x ∈ T` and compensates on a
private edge by containing a different element `y`.  Thus the two-literal
branches `x = false, y = true` cover every possible missing transversal. -/
theorem private_edge_escape
    [Fintype α]
    {H : Finset (Finset α)} {T S : Finset α}
    (hT : T ∈ blocker H) (hS : Hits H S) (havoid : ¬ T ⊆ S) :
    ∃ x ∈ T, x ∉ S ∧ ∃ E ∈ H, T ∩ E = {x} ∧
      ∃ y ∈ E, y ≠ x ∧ y ∈ S := by
  classical
  obtain ⟨x, hxT, hxS⟩ := Finset.not_subset.mp havoid
  obtain ⟨E, hEH, hprivate⟩ := blocker_private_edge hT hxT
  have hSE : ¬ Disjoint S E := hS E hEH
  obtain ⟨y, hyS, hyE⟩ := Finset.not_disjoint_iff.mp hSE
  have hyx : y ≠ x := by
    intro h
    exact hxS (h ▸ hyS)
  exact ⟨x, hxT, hxS, E, hEH, hprivate, y, hyE, hyx, hyS⟩

end IrrRAFEnumeration
