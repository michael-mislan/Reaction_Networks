import proofs.IrrRAFEnumeration.PrivateEdges

namespace IrrRAFEnumeration

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every member of `F` is contained in some region displayed by `C`. -/
def IsFullCover (C F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∃ S ∈ C, A ⊆ S

/-- The standard full cover built from one known clutter member. -/
def knownMemberFullCover (T : Finset α) : Finset (Finset α) :=
  insert T (T.image fun x => Finset.univ.erase x)

section StrongCover

variable [LinearOrder α]

/-- Elements of `T` preceding `x` in the chosen ground-set order. -/
def prior (T : Finset α) (x : α) : Finset α :=
  T.filter fun y => y < x

/-- The stronger Boros--Makino full cover.  For each `x ∈ T ∩ E`, its region
keeps `x` and deletes both the earlier elements of `T` and the rest of `E`. -/
def strongMemberFullCover (F : Finset (Finset α)) (T : Finset α) :
    Finset (Finset α) :=
  F.biUnion fun E => (T ∩ E).image fun x =>
    insert x ((Finset.univ \ prior T x) \ E)

/-- The stronger cover construction covers every minimal transversal.  The
least point where a transversal meets `T` determines an admissible region,
and minimality supplies the private edge used by that region. -/
theorem strongMemberFullCover_isFullCover
    (F : Finset (Finset α)) {T : Finset α} (hTF : T ∈ F) :
    IsFullCover (strongMemberFullCover F T) (blocker F) := by
  classical
  intro D hD
  have hhitT : ¬ Disjoint D T := (mem_blocker.mp hD).1 T hTF
  obtain ⟨z, hzD, hzT⟩ := Finset.not_disjoint_iff.mp hhitT
  have hDT : (D ∩ T).Nonempty :=
    ⟨z, Finset.mem_inter.mpr ⟨hzD, hzT⟩⟩
  let x := (D ∩ T).min' hDT
  have hxDT : x ∈ D ∩ T := Finset.min'_mem _ _
  have hxD : x ∈ D := (Finset.mem_inter.mp hxDT).1
  have hxT : x ∈ T := (Finset.mem_inter.mp hxDT).2
  obtain ⟨E, hEF, hprivate⟩ := blocker_private_edge hD hxD
  have hxE : x ∈ E := by
    have hxSingleton : x ∈ ({x} : Finset α) := by simp
    rw [← hprivate] at hxSingleton
    exact (Finset.mem_inter.mp hxSingleton).2
  let C := insert x ((Finset.univ \ prior T x) \ E)
  refine ⟨C, ?_, ?_⟩
  · simp only [strongMemberFullCover, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨E, hEF, x, Finset.mem_inter.mpr ⟨hxT, hxE⟩, rfl⟩
  · intro y hyD
    by_cases hyx : y = x
    · subst y
      simp [C]
    · have hyNotPrior : y ∉ prior T x := by
        intro hyPrior
        have hyTlt : y ∈ T ∧ y < x := by
          simpa [prior] using hyPrior
        have hyDT : y ∈ D ∩ T := Finset.mem_inter.mpr ⟨hyD, hyTlt.1⟩
        have hxy : x ≤ y := Finset.min'_le _ _ hyDT
        exact (not_lt_of_ge hxy) hyTlt.2
      have hyNotE : y ∉ E := by
        intro hyE
        have hyInter : y ∈ D ∩ E := Finset.mem_inter.mpr ⟨hyD, hyE⟩
        have : y = x := by simpa [hprivate] using hyInter
        exact hyx this
      simp [C, hyx, hyNotPrior, hyNotE]

omit [LinearOrder α] in
/-- Every blocker member surviving a strong-cover region must contain the
region's distinguished point.  This is the exact finite cardinality statement
behind the frequency shrink in the hybrid dualization recurrence. -/
theorem filterWithin_strongRegion_subset_vertexFiber
    (F G : Finset (Finset α)) (hGF : G ⊆ blocker F)
    (P E : Finset α) (hEF : E ∈ F) (x : α) :
    (G.filter fun D => D ⊆ insert x ((Finset.univ \ P) \ E)) ⊆
      G.filter fun D => x ∈ D := by
  classical
  intro D hD
  obtain ⟨hDG, hDregion⟩ := Finset.mem_filter.mp hD
  apply Finset.mem_filter.mpr ⟨hDG, ?_⟩
  by_contra hxD
  have hhitE : ¬ Disjoint D E :=
    (mem_blocker.mp (hGF hDG)).1 E hEF
  obtain ⟨y, hyD, hyE⟩ := Finset.not_disjoint_iff.mp hhitE
  have hyRegion := hDregion hyD
  simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ,
    true_and] at hyRegion
  rcases hyRegion with hyx | ⟨_hyNotP, hyNotE⟩
  · exact hxD (hyx ▸ hyD)
  · exact hyNotE hyE

omit [LinearOrder α] in
theorem filterWithin_strongRegion_card_le_vertexFiber
    (F G : Finset (Finset α)) (hGF : G ⊆ blocker F)
    (P E : Finset α) (hEF : E ∈ F) (x : α) :
    (G.filter fun D => D ⊆ insert x ((Finset.univ \ P) \ E)).card ≤
      (G.filter fun D => x ∈ D).card :=
  Finset.card_le_card
    (filterWithin_strongRegion_subset_vertexFiber F G hGF P E hEF x)

/-- The strong cover has at most one generated region per incidence of the
chosen member with an input edge, hence at most the total input incidence. -/
theorem strongMemberFullCover_card_le_incidence
    (F : Finset (Finset α)) (T : Finset α) :
    (strongMemberFullCover F T).card ≤ ∑ E ∈ F, E.card := by
  classical
  calc
    (strongMemberFullCover F T).card
        ≤ ∑ E ∈ F,
            ((T ∩ E).image fun x =>
              insert x ((Finset.univ \ prior T x) \ E)).card := by
          exact Finset.card_biUnion_le
    _ ≤ ∑ E ∈ F, (T ∩ E).card := by
          exact Finset.sum_le_sum fun E _hEF => Finset.card_image_le
    _ ≤ ∑ E ∈ F, E.card := by
          exact Finset.sum_le_sum fun E _hEF =>
            Finset.card_le_card (Finset.inter_subset_right)

end StrongCover

omit [DecidableEq α] in
theorem blocker_isClutter (F : Finset (Finset α)) : IsClutter (blocker F) := by
  intro A hA B hB hAB
  exact (mem_blocker.mp hB).2 (mem_blocker.mp hA).1 hAB

/-- A known member of a clutter yields a full cover with one region for the
member itself and one complement-of-a-point region for each of its elements.
This is the Elbassioni--Boros--Makino full-cover construction. -/
theorem knownMemberFullCover_isFullCover
    (F : Finset (Finset α)) (hF : IsClutter F)
    {T : Finset α} (hTF : T ∈ F) :
    IsFullCover (knownMemberFullCover T) F := by
  classical
  intro A hAF
  by_cases hAT : A = T
  · subst A
    exact ⟨T, by simp [knownMemberFullCover], Finset.Subset.rfl⟩
  · have hnsub : ¬ T ⊆ A := by
      intro hsub
      have hback : A ⊆ T := hF T hTF A hAF hsub
      exact hAT (Finset.Subset.antisymm hback hsub)
    obtain ⟨x, hxT, hxA⟩ := Finset.not_subset.mp hnsub
    refine ⟨Finset.univ.erase x, ?_, ?_⟩
    · simp only [knownMemberFullCover, Finset.mem_insert, Finset.mem_image]
      exact Or.inr ⟨x, hxT, rfl⟩
    · intro y hyA
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hyx
      exact hxA (hyx ▸ hyA)

theorem knownBlockerMemberFullCover_isFullCover
    (F : Finset (Finset α)) {T : Finset α} (hT : T ∈ blocker F) :
    IsFullCover (knownMemberFullCover T) (blocker F) :=
  knownMemberFullCover_isFullCover (blocker F) (blocker_isClutter F) hT

def filterWithin (F : Finset (Finset α)) (S : Finset α) :
    Finset (Finset α) :=
  F.filter fun A => A ⊆ S

omit [Fintype α] in
/-- Full covers are exactly sufficient for checking family equality region by
region. This is the combinatorial completeness half of full-cover duality. -/
theorem eq_iff_filterWithin_eq_of_fullCover
    (C F G : Finset (Finset α)) (hC : IsFullCover C F) (hGF : G ⊆ F) :
    G = F ↔ ∀ S ∈ C, filterWithin G S = filterWithin F S := by
  classical
  constructor
  · intro hEq S hSC
    rw [hEq]
  · intro hlocal
    apply Finset.Subset.antisymm hGF
    intro A hAF
    obtain ⟨S, hSC, hAS⟩ := hC A hAF
    have hAFilter : A ∈ filterWithin F S := by
      simp [filterWithin, hAF, hAS]
    rw [← hlocal S hSC] at hAFilter
    exact (Finset.mem_filter.mp hAFilter).1

theorem knownBlocker_complete_iff_regions
    (F G : Finset (Finset α)) (hGF : G ⊆ blocker F)
    {T : Finset α} (hT : T ∈ blocker F) :
    G = blocker F ↔
      ∀ S ∈ knownMemberFullCover T,
        filterWithin G S = filterWithin (blocker F) S :=
  eq_iff_filterWithin_eq_of_fullCover _ _ _
    (knownBlockerMemberFullCover_isFullCover F hT) hGF

/-- Regional completeness for the stronger ordered cover used by the hybrid
frequency/full-cover algorithm. -/
theorem strongBlocker_complete_iff_regions
    [LinearOrder α]
    (F G : Finset (Finset α)) (hGF : G ⊆ blocker F)
    {T : Finset α} (hTF : T ∈ F) :
    G = blocker F ↔
      ∀ S ∈ strongMemberFullCover F T,
        filterWithin G S = filterWithin (blocker F) S :=
  eq_iff_filterWithin_eq_of_fullCover _ _ _
    (strongMemberFullCover_isFullCover F hTF) hGF

end IrrRAFEnumeration
