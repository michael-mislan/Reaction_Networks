import proofs.DigraphRealizability.HornClosure

namespace DigraphRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

def replaceRule (L : Set (Rule E)) (q : Rule E) (B : Finset E) : Set (Rule E) :=
  {t | t ∈ L ∧ t ≠ q} ∪ {(B, q.2)}

theorem replacement {G L : Set (Rule E)} {B : Finset E} {q : Rule E}
    (hGL : G ⊆ L) (hL : SingleHead L) (hq : q ∈ L)
    (hbody : q.1 ⊆ B) (hfresh : q.2 ∉ Heads G)
    (hclosure : closure G q.1 = B) :
    SingleHead (replaceRule L q B) ∧
    insert (B, q.2) G ⊆ replaceRule L q B ∧
    ∀ X, Models (replaceRule L q B) X ↔ Models L X := by
  classical
  have keep : G ⊆ replaceRule L q B := by
    intro t ht
    left
    refine ⟨hGL ht, ?_⟩
    intro heq
    subst t
    exact hfresh ⟨q, ht, rfl⟩
  have unique : ∀ t ∈ L, t.2 = q.2 → t = q :=
    fun t ht heq => hL t ht q hq heq
  refine ⟨?_, ?_, ?_⟩
  · intro t ht v hv heq
    rcases ht with ht | ht <;> rcases hv with hv | hv
    · exact hL t ht.1 v hv.1 heq
    · have hv' : v = (B, q.2) := Set.mem_singleton_iff.mp hv
      subst v
      exact False.elim (ht.2 (unique t ht.1 heq))
    · have ht' : t = (B, q.2) := Set.mem_singleton_iff.mp ht
      subst t
      exact False.elim (hv.2 (unique v hv.1 heq.symm))
    · exact (Set.mem_singleton_iff.mp ht).trans (Set.mem_singleton_iff.mp hv).symm
  · intro t ht
    rcases ht with rfl | ht
    · exact Or.inr rfl
    · exact keep ht
  · intro X
    constructor
    · intro hm t ht htx
      by_cases heq : t = q
      · subst t
        have hGX : Models G X := fun a ha => hm a (keep ha)
        have hBX : B ⊆ X := hclosure ▸ closure_le hGX htx
        exact hm (B, q.2) (Or.inr rfl) hBX
      · exact hm t (Or.inl ⟨ht, heq⟩) htx
    · intro hm t ht htx
      rcases ht with ht | ht
      · exact hm t ht.1 htx
      · have heq : t = (B, q.2) := Set.mem_singleton_iff.mp ht
        subst t
        exact hm q hq (hbody.trans htx)

theorem extend_completion {G L : Set (Rule E)} {B : Finset E}
    (hGL : G ⊆ L) (hL : SingleHead L) (hB : MinimalResidual G L B) :
    ∃ r L', r ∉ B ∧ r ∉ Heads G ∧ SingleHead L' ∧
      insert (B, r) G ⊆ L' ∧
      (∀ X, Models L' X ↔ Models L X) ∧
      (∀ X, Models L X → B ⊆ X → r ∈ X) := by
  obtain ⟨q, hq, hb, hr, hf, hc⟩ := normalize hGL hL hB
  obtain ⟨hs, hi, he⟩ := replacement hGL hL hq hb hf hc
  exact ⟨q.2, replaceRule L q B, hr, hf, hs, hi, he,
    fun X hX hBX => hX q hq (hb.trans hBX)⟩
end DigraphRealizability

