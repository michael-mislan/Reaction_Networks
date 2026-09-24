import proofs.RAF.Frankl.GoodProjectionFibre
import proofs.RAF.Frankl.FeedbackLayers

namespace RAF.Frankl
open RAF RAFQueryCompilation
open scoped Classical

variable {M R : Type*} [DecidableEq M] [Fintype M] [Fintype R] [DecidableEq R]

noncomputable def goodProjectionFamily (Q : CRS M R) (C : Catalysis M R)
    (E : Finset R) : Finset (Finset R) :=
  (fixedFamily Q C).filter fun W => W ∩ E ∈ fixedFamily Q C

noncomputable def badProjectionFamily (Q : CRS M R) (C : Catalysis M R)
    (E : Finset R) : Finset (Finset R) :=
  (fixedFamily Q C).filter fun W => W ∩ E ∉ fixedFamily Q C

omit [Fintype M] in
theorem restrict_inter (U W : Finset R) :
    fromRestricted (toRestricted U W) = W ∩ U := by
  ext r
  simp only [mem_fromRestricted,mem_toRestricted,Finset.mem_inter]
  tauto

theorem good_projection_subset_core (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (E W : Finset R)
    (hw : W ∩ E ∈ fixedFamily Q C) : W ∩ E ⊆ evaluate Q C E := by
  rcases (mem_fixedFamily Q C _).mp hw with he | he
  · simp [he]
  · exact raf_subset_evaluate Q C Finset.inter_subset_right he

theorem good_projection_inter_core (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (E W : Finset R)
    (hw : W ∩ E ∈ fixedFamily Q C) : W ∩ evaluate Q C E = W ∩ E := by
  apply Finset.Subset.antisymm
  · intro r hr
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hr).1,
      evaluate_subset Q C E (Finset.mem_inter.mp hr).2⟩
  · intro r hr
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hr).1,
      good_projection_subset_core Q C E W hw hr⟩

theorem good_projection_exterior_disjoint (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (E W : Finset R)
    (hw : W ∩ E ∈ fixedFamily Q C) : Disjoint (W \ evaluate Q C E) E := by
  apply Finset.disjoint_left.mpr
  intro r hr he
  exact (Finset.mem_sdiff.mp hr).2 (good_projection_subset_core Q C E W hw
    (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hr).1,he⟩))

omit [Fintype M] [Fintype R] in
theorem restricted_union_inter (U E T : Finset R) (hUE : U ⊆ E)
    (hTE : Disjoint T E) (S : Finset {r // r ∈ U}) :
    (fromRestricted S ∪ T) ∩ E = fromRestricted S := by
  ext r
  constructor
  · intro hr
    rcases Finset.mem_inter.mp hr with ⟨hr,he⟩
    rcases Finset.mem_union.mp hr with hs | ht
    · exact hs
    · exact (Finset.disjoint_left.mp hTE ht he).elim
  · intro hs
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left T hs,
      hUE ((mem_fromRestricted S r).mp hs).1⟩

theorem good_family_fibre_image (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (E T : Finset R) (hTE : Disjoint T E) :
    ((goodProjectionFamily Q C E).filter (fun W => W \ evaluate Q C E = T)).image
      (toRestricted (evaluate Q C E)) = goodProjectionFibre Q C (evaluate Q C E) T := by
  have hTU : Disjoint T (evaluate Q C E) := hTE.mono_right (evaluate_subset Q C E)
  ext S
  simp only [Finset.mem_image,Finset.mem_filter,goodProjectionFamily,
    goodProjectionFibre,Finset.mem_powerset,Finset.subset_univ,true_and]
  constructor
  · rintro ⟨W,⟨⟨hw,hp⟩,ht⟩,rfl⟩
    constructor
    · rw [← ht,core_exterior_reconstruct]
      exact hw
    · rw [restrict_inter,good_projection_inter_core Q C E W hp]
      exact hp
  · rintro ⟨hw,hp⟩
    refine ⟨fromRestricted S ∪ T,⟨⟨hw,?_⟩,
      core_extend_exterior _ T hTU S⟩,core_extend_restrict _ T hTU S⟩
    rwa [restricted_union_inter _ E T (evaluate_subset Q C E) hTE S]

theorem good_family_fibre_average (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (E T : Finset R)
    (hE : ∀ r ∈ E, SeedReaction Q r) (hne : (evaluate Q C E).Nonempty) :
    ((goodProjectionFamily Q C E).filter (fun W => W \ evaluate Q C E = T)).card *
      Fintype.card {r // r ∈ evaluate Q C E} ≤
    2 * ∑ W ∈ (goodProjectionFamily Q C E).filter (fun W => W \ evaluate Q C E = T),
      (toRestricted (evaluate Q C E) W).card := by
  by_cases ht : Disjoint T E
  · have hu : IsRAF Q C (evaluate Q C E) :=
      (isRAF_iff_nonempty_prune_eq Q C _).mpr ⟨hne,evaluate_fixed Q C E⟩
    have h := goodProjectionFibre_average Q C (evaluate Q C E) T hu
      (fun r hr => hE r (evaluate_subset Q C E hr))
    rw [← good_family_fibre_image Q C E T ht] at h
    have hi : (((goodProjectionFamily Q C E).filter
        (fun W => W \ evaluate Q C E = T)) : Set (Finset R)).InjOn
        (toRestricted (evaluate Q C E)) := by
      apply (core_restrict_injOn Q C (evaluate Q C E) T).mono
      intro W hw
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1,
        (Finset.mem_filter.mp hw).2⟩
    rwa [Finset.card_image_iff.mpr hi,Finset.sum_image hi] at h
  · have he : (goodProjectionFamily Q C E).filter
        (fun W => W \ evaluate Q C E = T) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro W hw
      have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
      have hd := good_projection_exterior_disjoint Q C E W hp
      rw [(Finset.mem_filter.mp hw).2] at hd
      exact ht hd
    simp [he]

theorem good_projection_average (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (E : Finset R)
    (hE : ∀ r ∈ E, SeedReaction Q r) (hne : (evaluate Q C E).Nonempty) :
    (evaluate Q C E).card * (goodProjectionFamily Q C E).card ≤
      2 * ∑ W ∈ goodProjectionFamily Q C E, (W ∩ evaluate Q C E).card := by
  let F := goodProjectionFamily Q C E
  let U := evaluate Q C E
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset R)))
    (fun T _ => good_family_fibre_average Q C E T hE hne)
  have hc : (∑ T : Finset R, (F.filter (fun W => W \ U = T)).card) = F.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter F
      (Finset.univ : Finset (Finset R)) (fun W => W \ U)
  have hs : (∑ T : Finset R, ∑ W ∈ F.filter (fun W => W \ U = T),
      (toRestricted U W).card) = ∑ W ∈ F, (toRestricted U W).card := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro W _
    simp
  change (∑ T : Finset R, (F.filter (fun W => W \ U = T)).card *
    Fintype.card {r // r ∈ U}) ≤
    ∑ T : Finset R, 2 * ∑ W ∈ F.filter (fun W => W \ U = T),
      (toRestricted U W).card at hsum
  simp only [← Finset.sum_mul,← Finset.mul_sum] at hsum
  rw [hc,hs] at hsum
  have hcard : ∀ W : Finset R, (toRestricted U W).card = (W ∩ U).card := by
    intro W
    rw [← restrict_inter U W]
    simp [fromRestricted]
  simpa only [hcard,Fintype.card_coe,Nat.mul_comm] using hsum

/-- Literal defect bound on the original elementary module's active maxRAF.
There is no unproved good-average premise in this public theorem. -/
theorem feedback_defect_bound (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (E : Finset R)
    (hE : ∀ r ∈ E, SeedReaction Q r) (hne : (evaluate Q C E).Nonempty) :
    (evaluate Q C E).card * ((fixedFamily Q C).card - (badProjectionFamily Q C E).card) +
      2 * ∑ W ∈ badProjectionFamily Q C E, (W ∩ evaluate Q C E).card ≤
      2 * ∑ W ∈ fixedFamily Q C, (W ∩ evaluate Q C E).card := by
  apply defect_bound_of_good_average _ _ _ (Finset.filter_subset _ _)
  have he : fixedFamily Q C \ badProjectionFamily Q C E = goodProjectionFamily Q C E := by
    ext W
    simp only [badProjectionFamily,goodProjectionFamily,Finset.mem_sdiff,Finset.mem_filter]
    tauto
  dsimp only [badProjectionFamily] at he
  rw [he]
  exact good_projection_average Q C E hE hne

end RAF.Frankl
