import proofs.RAF.Frankl.ElementaryHorn
import proofs.RAF.Frankl.ElementaryConditioning
import proofs.RAF.Frankl.FibreCounting

namespace RAF.Frankl

open RAF
open scoped Classical

variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

def extensionSupport (Q : CRS M R) (C : Catalysis M R)
    (W : Finset R) (r : R) : Prop :=
  (∃ x ∈ Q.food, C x r) ∨ ∃ p ∈ W, ∃ x ∈ Q.outputs p, C x r

omit [Fintype R] [DecidableEq R] in
theorem extensionSupport_mono (Q : CRS M R) (C : Catalysis M R)
    {A B : Finset R} (hAB : A ⊆ B) {r : R} :
    extensionSupport Q C A r → extensionSupport Q C B r := by
  rintro (hf | ⟨p,hp,hc⟩)
  · exact Or.inl hf
  · exact Or.inr ⟨p,hAB hp,hc⟩

theorem fixedFamily_iff_food_support (Q : CRS M R) (C : Catalysis M R)
    (W : Finset R) :
    W ∈ fixedFamily Q C ↔ FoodGenerated Q W ∧ ∀ r ∈ W, extensionSupport Q C W r := by
  rw [mem_fixedFamily]
  constructor
  · rintro (rfl | h)
    · simp [foodGenerated_empty]
    · exact (isRAF_iff_foodGenerated_and_productGraph Q C W).mp h |>.2
  · intro h
    by_cases he : W = ∅
    · exact Or.inl he
    · exact Or.inr ((isRAF_iff_foodGenerated_and_productGraph Q C W).mpr
        ⟨Finset.nonempty_iff_ne_empty.mpr he,h⟩)

noncomputable def extensionBody (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (r : {r // r ∈ U}) : Finset {r // r ∈ U} :=
  if extensionSupport Q C T r.1 then {r}
  else Finset.univ.filter fun p => ∃ x ∈ Q.outputs p.1, C x r.1

def exteriorGood (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (S : Finset {r // r ∈ U}) : Prop :=
  FoodGenerated Q (fromRestricted S ∪ T) ∧
    ∀ r ∈ T, extensionSupport Q C (fromRestricted S ∪ T) r

omit [Fintype R] in
theorem fromRestricted_mono {U : Finset R}
    {A B : Finset {r // r ∈ U}} (hab : A ⊆ B) :
    fromRestricted A ⊆ fromRestricted B := by
  intro r hr
  obtain ⟨hu,hs⟩ := (mem_fromRestricted A r).mp hr
  exact (mem_fromRestricted B r).mpr ⟨hu,hab hs⟩

omit [Fintype R] in
theorem extensionBody_hit_iff (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (S : Finset {r // r ∈ U})
    (r : {r // r ∈ U}) (hr : r ∈ S) :
    (∃ p ∈ S, p ∈ extensionBody Q C U T r) ↔
      extensionSupport Q C (fromRestricted S ∪ T) r.1 := by
  classical
  by_cases ho : extensionSupport Q C T r.1
  · constructor
    · intro _
      exact extensionSupport_mono Q C Finset.subset_union_right ho
    · intro _
      exact ⟨r,hr,by simp [extensionBody,ho]⟩
  · simp only [extensionBody,if_neg ho,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨p,hp,hc⟩
      exact Or.inr ⟨p.1, Finset.mem_union_left T
        ((mem_fromRestricted S p.1).mpr ⟨p.2,hp⟩),hc⟩
    · rintro (hf | ⟨p,hp,hc⟩)
      · exact (ho (Or.inl hf)).elim
      · rcases Finset.mem_union.mp hp with hp | hp
        · obtain ⟨hu,hs⟩ := (mem_fromRestricted S p).mp hp
          exact ⟨⟨p,hu⟩,hs,hc⟩
        · exact (ho (Or.inr ⟨p,hp,hc⟩)).elim

omit [Fintype R] [DecidableEq R] in
theorem extensionBody_nonempty (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (hu : IsRAF Q C U) (r : {r // r ∈ U}) :
    (extensionBody Q C U T r).Nonempty := by
  classical
  have hg := (isRAF_iff_foodGenerated_and_productGraph Q C U).mp hu |>.2.2
  by_cases ho : extensionSupport Q C T r.1
  · simp [extensionBody,ho]
  · rcases hg r.1 r.2 with hf | ⟨p,hp,hc⟩
    · exact (ho (Or.inl hf)).elim
    · exact ⟨⟨p,hp⟩, by simp [extensionBody,ho,hc]⟩

theorem extension_fibre_iff (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (S : Finset {r // r ∈ U}) :
    fromRestricted S ∪ T ∈ fixedFamily Q C ↔
      exteriorGood Q C U T S ∧
        ¬ dependencyHornDNF (extensionBody Q C U T) (Finset.univ \ S) := by
  rw [fixedFamily_iff_food_support,not_dependencyHorn_compl_iff]
  constructor
  · rintro ⟨hf,hg⟩
    refine ⟨⟨hf,fun r hr => hg r (Finset.mem_union_right _ hr)⟩,?_⟩
    intro r hr
    apply (extensionBody_hit_iff Q C U T S r hr).mpr
    exact hg r.1 (Finset.mem_union_left T
      ((mem_fromRestricted S r.1).mpr ⟨r.2,hr⟩))
  · rintro ⟨⟨hf,hT⟩,hS⟩
    refine ⟨hf,?_⟩
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨hu,hs⟩ := (mem_fromRestricted S r).mp hr
      exact (extensionBody_hit_iff Q C U T S ⟨r,hu⟩ hs).mp (hS ⟨r,hu⟩ hs)
    · exact hT r hr

omit [Fintype R] in
theorem exteriorGood_mono (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (hE : ∀ r ∈ U, SeedReaction Q r)
    {A B : Finset {r // r ∈ U}} (hAB : A ⊆ B) :
    exteriorGood Q C U T A → exteriorGood Q C U T B := by
  rintro ⟨hfg,hcat⟩
  have hm : fromRestricted A ∪ T ⊆ fromRestricted B ∪ T :=
    Finset.union_subset_union (fromRestricted_mono hAB) (Finset.Subset.refl T)
  refine ⟨?_,fun r hr => extensionSupport_mono Q C hm (hcat r hr)⟩
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr
  · obtain ⟨hu,_⟩ := (mem_fromRestricted B r).mp hr
    exact ⟨0,hE r hu⟩
  · obtain ⟨k,hk⟩ := hfg r (Finset.mem_union_right _ hr)
    exact ⟨k,fun x hx => closureAt_mono_reactions Q hm k (hk hx)⟩

noncomputable def extensionFibre (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) : Finset (Finset {r // r ∈ U}) :=
  Finset.univ.powerset.filter fun S => fromRestricted S ∪ T ∈ fixedFamily Q C

theorem extensionFibre_average (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (hU : IsRAF Q C U) (hE : ∀ r ∈ U, SeedReaction Q r) :
    (extensionFibre Q C U T).card * Fintype.card {r // r ∈ U} ≤
      2 * ∑ S ∈ extensionFibre Q C U T, S.card := by
  classical
  let d : {r // r ∈ U} → {r // r ∈ U} := fun r =>
    Classical.choose (extensionBody_nonempty Q C U T hU r)
  have hd : ∀ r, d r ∈ extensionBody Q C U T r := fun r =>
    Classical.choose_spec (extensionBody_nonempty Q C U T hU r)
  have h := supported_upward_average (extensionBody Q C U T) d hd
    (exteriorGood Q C U T) (fun hab => exteriorGood_mono Q C U T hE hab)
  have heq : extensionFibre Q C U T = Finset.univ.powerset.filter
      (fun S => exteriorGood Q C U T S ∧
        ¬ dependencyHornDNF (extensionBody Q C U T) (Finset.univ \ S)) := by
    ext S
    simp only [extensionFibre,Finset.mem_filter,extension_fibre_iff]
  rw [heq]
  exact h

end RAF.Frankl
