import proofs.DigraphRealizability.IntervalDeletion

namespace DigraphRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

def LegalStep (F U : Finset (Finset E)) (H : Finset E) (S : Finset E) (r : E) : Prop :=
  (S ∈ U ∧ S ∉ F) ∧
  (∀ T ∈ U, T ∉ F → S ⊆ T → T = S) ∧
  r ∈ S ∧ (∀ T ∈ F, T ⊆ S → r ∉ T) ∧ r ∉ H

instance (F U : Finset (Finset E)) (H S : Finset E) (r : E) :
    Decidable (LegalStep F U H S r) := by
  unfold LegalStep
  infer_instance

def checkTrace (F U : Finset (Finset E)) (H : Finset E) :
    List (Finset E × E) → Bool
  | [] => decide (U = F)
  | (S,r) :: xs => decide (LegalStep F U H S r) &&
      checkTrace F (deleteInterval U S r) (insert r H) xs

theorem checkTrace_sound {F U : Finset (Finset E)} {H : Finset E}
    {xs : List (Finset E × E)} (h : checkTrace F U H xs = true) :
    Peels F U (H : Set E) := by
  induction xs generalizing U H with
  | nil =>
    have eq : U = F := of_decide_eq_true h
    subst U
    exact Peels.done _
  | cons q xs ih =>
    obtain ⟨S,r⟩ := q
    simp only [checkTrace, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨bad, maximal, inside, absent, fresh⟩, ht⟩ := h
    have tail := ih ht
    simp only [Finset.coe_insert] at tail
    exact Peels.step bad maximal inside absent fresh tail

theorem Peels.exists_checked_trace {F U : Finset (Finset E)} {H : Set E}
    (run : Peels F U H) :
    ∀ Hf : Finset E, (Hf : Set E) = H → ∃ xs, checkTrace F U Hf xs = true := by
  induction run with
  | done H =>
    intro Hf _
    exact ⟨[], by simp [checkTrace]⟩
  | @step U H S r bad maximal inside absent fresh _ ih =>
    intro Hf heq
    have ht : ((insert r Hf : Finset E) : Set E) = insert r H := by
      simp [heq]
    obtain ⟨xs,hxs⟩ := ih (insert r Hf) ht
    refine ⟨(S,r) :: xs, ?_⟩
    have hlegal : LegalStep F U Hf S r :=
      ⟨bad, maximal, inside, absent, fun hr => fresh (heq ▸ hr)⟩
    simp [checkTrace, hlegal, hxs]

theorem intrinsic_iff_checked_trace (F : Finset (Finset E)) :
    IntrinsicPeelable F ↔ ∃ xs, checkTrace F Finset.univ ∅ xs = true := by
  constructor
  · intro h
    exact Peels.exists_checked_trace h ∅ (by simp)
  · rintro ⟨xs,hxs⟩
    simpa [IntrinsicPeelable] using checkTrace_sound hxs

theorem digraphRealizable_iff_checked_trace (F : Finset (Finset E)) :
    (∃ P : E → Finset E, ∀ S, S ∈ F ↔ RAFInteriorRealizability.PredSupported P S) ↔
      ∃ xs, checkTrace F Finset.univ ∅ xs = true :=
  (digraphRealizable_iff_intrinsicPeeling F).trans (intrinsic_iff_checked_trace F)
end DigraphRealizability
