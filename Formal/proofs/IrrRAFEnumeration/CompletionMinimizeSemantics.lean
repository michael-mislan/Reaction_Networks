import proofs.IrrRAFEnumeration.CompletionMinimizeLoop

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def deletionStates {r : Nat} (P : Finset (Fin r) → Prop) [DecidablePred P]
    (U : Finset (Fin r)) : Nat → Finset (Fin r)
  | 0 => U
  | i+1 =>
    let V := deletionStates P U i
    if hi : i < r then if P (V.erase ⟨i,hi⟩) then V.erase ⟨i,hi⟩ else V else V

theorem deletionStates_step {r : Nat} (P : Finset (Fin r) → Prop) [DecidablePred P]
    (U : Finset (Fin r)) (i : Nat) (hi : i < r) : deletionStates P U (i+1) =
      if P ((deletionStates P U i).erase ⟨i,hi⟩)
      then (deletionStates P U i).erase ⟨i,hi⟩ else deletionStates P U i := by
  simp only [deletionStates,dif_pos hi]

theorem deletionStates_available {r : Nat} (P : Finset (Fin r) → Prop) [DecidablePred P]
    (U : Finset (Fin r)) (hU : P U) (i : Nat) : P (deletionStates P U i) := by
  induction i with
  | zero => exact hU
  | succ i ih =>
    simp only [deletionStates]
    split
    · split
      · assumption
      · exact ih
    · exact ih

theorem deletionStates_minimal {r : Nat} (P : Finset (Fin r) → Prop) [DecidablePred P]
    (hmono : Monotone P) (U : Finset (Fin r)) (hU : P U) :
    Minimal P (deletionStates P U r) := by
  have hdel : ∀ i, i ≤ r → ∀ j : Fin r, j.val < i → j ∈ deletionStates P U i →
      ¬P ((deletionStates P U i).erase j) := by
    intro i
    induction i with
    | zero => intro _ j hj; omega
    | succ i ih =>
      intro hir j hj hjmem
      have hi : i < r := by omega
      rw [deletionStates_step P U i hi] at hjmem ⊢
      by_cases hs : P ((deletionStates P U i).erase ⟨i,hi⟩)
      · rw [if_pos hs] at hjmem ⊢
        have hji : j.val < i := by
          have hn := (Finset.mem_erase.mp hjmem).1
          have hne : j.val ≠ i := by
            intro he
            exact hn (Fin.ext he)
          omega
        intro hP
        exact ih (by omega) j hji (Finset.mem_erase.mp hjmem).2
          (hmono (Finset.erase_subset_erase j (Finset.erase_subset _ _)) hP)
      · rw [if_neg hs] at hjmem ⊢
        by_cases he : j.val = i
        · have he' : j = (⟨i,hi⟩ : Fin r) := Fin.ext he
          simpa only [he'] using hs
        · exact ih (by omega) j (by omega) hjmem
  refine ⟨deletionStates_available P U hU r,?_⟩
  intro V hV hVU j hj
  by_contra hn
  have hv : V ⊆ (deletionStates P U r).erase j := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by intro he; subst x; exact hn hx,hVU hx⟩
  exact hdel r le_rfl j j.isLt hj (hmono hv hV)

/-- The runtime loop reaches a minimal true container, provided its actual
decision subprogram has a uniform bound over the generated trials. -/
theorem minimizeTM_correct {r k : Nat} (call : TM (bufferedCount k))
    (P : Finset (Fin r) → Prop) [DecidablePred P] (hmono : Monotone P)
    (U : Finset (Fin r)) (hU : P U) (base blocks : List Bool)
    (inp : Tape) (hp : Parked inp) (b : Nat)
    (hcall : ∀ i (hi : i < r), call.HoareTime
      (EmitPred inp (completionWork k ((deletionStates P U i).erase ⟨i,hi⟩) base blocks) [])
      (completionResult k ((deletionStates P U i).erase ⟨i,hi⟩) base blocks inp
        (P ((deletionStates P U i).erase ⟨i,hi⟩))) b) :
    (minimizeTM call).HoareTime (EmitPred inp (minimizeWork k U base blocks 0) [])
      (fun a w out => ∃ V, Minimal P V ∧ EmitPred inp (minimizeWork k V base blocks r) [] a w out)
      (r*(b+12*r+33)+(r+2)) := by
  have h := minimizeTM_sequence_correct call P (deletionStates P U) base blocks inp hp b
    (fun i _ => deletionStates_available P U hU i) (deletionStates_step P U) hcall
  exact h.strengthen_post (fun _ _ _ hp => ⟨_,deletionStates_minimal P hmono U hU,hp⟩)

end IrrRAFEnumeration.CompletionQuery
