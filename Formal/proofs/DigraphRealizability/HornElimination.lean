import proofs.DigraphRealizability.ResidualNormalization
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Tauto

namespace DigraphRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

def trim (U : Finset (Finset E)) (B : Finset E) (r : E) : Finset (Finset E) :=
  U.filter fun X => ¬ B ⊆ X ∨ r ∈ X

/-- A family-only rule: choose a minimal residual set and a fresh forced coordinate. -/
inductive Eliminates (K : Finset (Finset E)) :
    Finset (Finset E) → Set E → Prop
  | done (H) : Eliminates K K H
  | step {U H B r}
      (bad : B ∈ U ∧ B ∉ K)
      (minimal : ∀ T ∈ U, T ∉ K → T ⊆ B → T = B)
      (outside : r ∉ B)
      (forced : ∀ X ∈ K, B ⊆ X → r ∈ X)
      (fresh : r ∉ H)
      (tail : Eliminates K (trim U B r) (insert r H)) :
      Eliminates K U H

omit [Fintype E] [DecidableEq E] in
theorem models_insert (G : Set (Rule E)) (B X : Finset E) (r : E) :
    Models (insert (B,r) G) X ↔ Models G X ∧ (B ⊆ X → r ∈ X) := by
  constructor
  · intro h
    exact ⟨fun q hq => h q (Set.mem_insert_of_mem _ hq),
      h (B,r) (Set.mem_insert _ _)⟩
  · rintro ⟨hG, hB⟩ q (rfl | hq) hqX
    · exact hB hqX
    · exact hG q hq hqX

omit [Fintype E] [DecidableEq E] in
theorem heads_insert (G : Set (Rule E)) (B : Finset E) (r : E) :
    Heads (insert (B,r) G) = insert r (Heads G) := by
  ext v
  constructor
  · rintro ⟨q, (rfl | hq), heq⟩
    · exact Or.inl heq.symm
    · exact Or.inr ⟨q, hq, heq⟩
  · rintro (rfl | ⟨q, hq, heq⟩)
    · exact ⟨(B,v), Or.inl rfl, rfl⟩
    · exact ⟨q, Or.inr hq, heq⟩

omit [Fintype E] [DecidableEq E] in
theorem singleHead_insert {G : Set (Rule E)} {B : Finset E} {r : E}
    (hs : SingleHead G) (hf : r ∉ Heads G) : SingleHead (insert (B,r) G) := by
  intro q hq t ht he
  rcases hq with rfl | hq <;> rcases ht with rfl | ht
  · rfl
  · exact False.elim (hf ⟨t, ht, he.symm⟩)
  · exact False.elim (hf ⟨q, hq, he⟩)
  · exact hs q hq t ht he

/-- Completeness has no hypothesized normalizer: it invokes the proved replacement lemma. -/
theorem elimination_complete (K U : Finset (Finset E)) :
    ∀ G L : Set (Rule E), G ⊆ L → SingleHead L →
    (∀ X, X ∈ U ↔ Models G X) →
    (∀ X, X ∈ K ↔ Models L X) →
    Eliminates K U (Heads G) := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro G L hGL hL hU hK
    by_cases heq : U = K
    · subst U
      exact Eliminates.done _
    have hKU : K ⊆ U := by
      intro X hX
      exact (hU X).mpr (fun q hq => (hK X).mp hX q (hGL hq))
    have hn : (U \ K).Nonempty := by
      by_contra h
      have : U ⊆ K := Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp h)
      exact heq (Finset.Subset.antisymm this hKU)
    obtain ⟨B, hB, hmin⟩ := (U \ K).exists_min_image Finset.card hn
    obtain ⟨hBU, hBK⟩ := Finset.mem_sdiff.mp hB
    have minimal : ∀ T ∈ U, T ∉ K → T ⊆ B → T = B := by
      intro T hTU hTK hTB
      exact Finset.eq_of_subset_of_card_le hTB (hmin T (Finset.mem_sdiff.mpr ⟨hTU,hTK⟩))
    have hres : MinimalResidual G L B := by
      refine ⟨(hU B).mp hBU, fun h => hBK ((hK B).mpr h), ?_⟩
      intro T hTG hTL hTB
      exact minimal T ((hU T).mpr hTG) (fun h => hTL ((hK T).mp h)) hTB
    obtain ⟨r, L', hr, hf, hs, hi, hm, hforce⟩ := extend_completion hGL hL hres
    have htrim : trim U B r ⊂ U := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro eq
      have : B ∈ trim U B r := eq.symm ▸ hBU
      have cond := (Finset.mem_filter.mp this).2
      exact cond.elim (fun h => h (Finset.Subset.refl B)) hr
    have hmodels : ∀ X, X ∈ trim U B r ↔ Models (insert (B,r) G) X := by
      intro X
      rw [models_insert]
      simp only [trim, Finset.mem_filter, hU X]
      tauto
    have htarget : ∀ X, X ∈ K ↔ Models L' X := fun X => (hK X).trans (hm X).symm
    have tail := ih (trim U B r) htrim (insert (B,r) G) L' hi hs hmodels htarget
    rw [heads_insert] at tail
    exact Eliminates.step ⟨hBU,hBK⟩ minimal hr
      (fun X hX => hforce X ((hK X).mp hX)) hf tail

omit [Fintype E] in
theorem elimination_sound {K U : Finset (Finset E)} {H : Set E}
    (run : Eliminates K U H) :
    ∀ G : Set (Rule E), SingleHead G → Heads G ⊆ H →
      (∀ X, X ∈ U ↔ Models G X) →
      ∃ L : Set (Rule E), SingleHead L ∧ ∀ X, X ∈ K ↔ Models L X := by
  classical
  induction run with
  | done H =>
    intro G hs _ hm
    exact ⟨G, hs, hm⟩
  | @step U H B r _ _ _ _ fresh _ ih =>
    intro G hs hh hm
    have hf : r ∉ Heads G := fun h => fresh (hh h)
    apply ih (insert (B,r) G) (singleHead_insert hs hf)
    · rw [heads_insert]
      exact Set.insert_subset_insert hh
    · intro X
      rw [models_insert]
      simp only [trim, Finset.mem_filter, hm X]
      tauto

theorem singleHead_iff_eliminates (K : Finset (Finset E)) :
    (∃ L : Set (Rule E), SingleHead L ∧ ∀ X, X ∈ K ↔ Models L X) ↔
      Eliminates K Finset.univ ∅ := by
  classical
  constructor
  · rintro ⟨L, hs, hm⟩
    have h := elimination_complete K Finset.univ ∅ L (Set.empty_subset _) hs
      (by intro X; simp [Models]) hm
    simpa [Heads] using h
  · intro h
    exact elimination_sound h ∅ (by simp [SingleHead]) (by simp [Heads])
      (by intro X; simp [Models])
end DigraphRealizability
