import proofs.IrrRAFEnumeration.CompletionCapture

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def clearedWork {n : Nat} (work : Fin n → Tape) (xs : List (Fin n)) : Fin n → Tape :=
  fun i => if i ∈ xs then parkedInput [] else work i

def clearManyTM {n : Nat} (fuel : Fin n) : List (Fin n) → TM n
  | [] => skipTM
  | i :: xs => seqTM (resetScratchTM fuel i) (clearManyTM fuel xs)

theorem blank_footprint {b : Nat} (hb : 1 ≤ b) : ScratchFootprint b (parkedInput []) := by
  refine ⟨Tape.StartInvariant.init_nil.move Dir3.right,hb,?_⟩
  intro j hj
  have hj0 : j ≠ 0 := by omega
  simp [parkedInput,Tape.init,hj0]

/-- Reset a fixed list of scratch tapes, preserving the computed fuel and every
unlisted tape. Duplicate indices are permitted and do not affect correctness. -/
theorem clearManyTM_correct {n : Nat} (fuel : Fin n) (xs : List (Fin n))
    (b : Nat) (hb : 1 ≤ b) (hnot : fuel ∉ xs) (inp : Tape) (work : Fin n → Tape)
    (ys : List Bool) (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hf : work fuel = regTape b)
    (hs : ∀ i ∈ xs, ScratchFootprint b (work i)) :
    (clearManyTM fuel xs).HoareTime (EmitPred inp work ys)
      (EmitPred inp (clearedWork work xs) ys) (xs.length*(6*b+10)+1) := by
  induction xs generalizing work with
  | nil => simpa [clearManyTM,clearedWork] using skipTM_hoareTime inp work ys hp hw
  | cons i xs ih =>
    have hi : i ≠ fuel := by intro he; subst i; exact hnot (by simp)
    have hrest : fuel ∉ xs := fun h => hnot (by simp [h])
    have hsi := hs i (by simp)
    let W := Function.update work i (parkedInput [])
    have hw' : ∀ j, Parked (W j) := by
      intro j
      by_cases hj : j = i
      · subst j
        simpa [W] using parkedInput_parked ([] : List Bool)
      · simpa [W,Function.update_of_ne hj] using hw j
    have hf' : W fuel = regTape b := by
      simpa [W,Function.update_of_ne (Ne.symm hi)] using hf
    have hs' : ∀ j ∈ xs, ScratchFootprint b (W j) := by
      intro j hj
      by_cases he : j = i
      · subst j
        simpa [W] using blank_footprint hb
      · simpa [W,Function.update_of_ne he] using hs j (by simp [hj])
    have h1 := (resetScratchTM_correct fuel i hi b inp work ys hp hw hf hsi.1.1 hsi.2.2).mono_bound
      (by have := hsi.2.1; omega : (work i).head+5*b+9 ≤ 6*b+9)
    have h2 := ih hrest W hw' hf' hs'
    have he : clearedWork W xs = clearedWork work (i :: xs) := by
      funext j
      by_cases hx : j ∈ xs
      · simp [clearedWork,hx]
      · by_cases hj : j = i
        · subst j
          simp [clearedWork,W,hx]
        · simp [clearedWork,W,hx,hj]
    rw [he] at h2
    have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw' ys) h2
    exact h.mono_bound (by simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega)

end IrrRAFEnumeration.CompletionQuery
