import proofs.IrrRAFEnumeration.CompletionReset

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def lowTape (k : Nat) (i : Fin 10) : Fin (bufferedCount k) := ⟨i.val,by
  have := i.isLt
  unfold bufferedCount
  omega⟩

theorem completionScratch_mem_iff {k : Nat} (i : Fin (bufferedCount k)) :
    i ∈ completionScratch k ↔ 10 ≤ i.val := by
  constructor
  · exact completionScratch_ge
  · intro hi
    have hb := i.isLt
    have hx : i.val-10 < k+2 := by unfold bufferedCount at hb; omega
    apply List.mem_map.mpr
    refine ⟨⟨i.val-10,hx⟩,by simp,?_⟩
    apply Fin.ext
    dsimp
    omega

theorem bufferedWork_prefix {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp verdict : Tape) (bound : Nat) (answer : Prop)
    (inner : Fin (7+(3+k)+1) → Tape)
    (h : clockedSATPost q k U base blocks query inp bound answer inp inner verdict)
    (i : Fin 7) :
    bufferedWork inner verdict ⟨i.val,by have := i.isLt; omega⟩ =
      dynamicWork U (1+r) r base blocks i := by
  obtain ⟨_,inside,he,_,_,_,_,_⟩ := h
  have hi := i.isLt
  have h1 : i.val < 7+(3+k)+1 := by omega
  have h2 : i.val < 7+(3+k) := by omega
  simp [bufferedWork,frameWork,h1,h2,hi,he,placedClockWork,placeWorkInMiddle,
    queryDecisionWork,queryPrefix]

theorem bufferedWork_clock {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp verdict : Tape) (bound : Nat) (answer : Prop)
    (inner : Fin (7+(3+k)+1) → Tape)
    (h : clockedSATPost q k U base blocks query inp bound answer inp inner verdict)
    (i : Fin 3) :
    bufferedWork inner verdict ⟨7+i.val,by have := i.isLt; omega⟩ =
      clockWork q query.length i := by
  obtain ⟨_,inside,he,hclock,_,_,_,_⟩ := h
  have hi := i.isLt
  have h1 : 7+i.val < 7+(3+k)+1 := by omega
  have h2 : 7+i.val < 7+(3+k+1) := by omega
  simpa [bufferedWork,frameWork,h1,h2,he,placedClockWork,placeWorkInMiddle,
    placeWorkCoord] using hclock i

def resetWork {k : Nat} (inner : Fin (7+(3+k)+1) → Tape) (verdict : Tape) :=
  clearedWork (capturedWork inner verdict) (completionScratch k)

theorem resetWork_low {k : Nat} (inner : Fin (7+(3+k)+1) → Tape) (verdict : Tape)
    (i : Fin 10) (hi : i.val ≠ 3) :
    resetWork inner verdict (lowTape k i) = normalizeScratchHead
      (bufferedWork inner verdict (lowTape k i)) := by
  have hnot : lowTape k i ∉ completionScratch k := by
    rw [completionScratch_mem_iff]
    have := i.isLt
    simp only [lowTape]
    omega
  have ho : lowTape k i ≠ completionOutput k := by
    intro he
    have hh := congrArg Fin.val he
    have := i.isLt
    simp only [lowTape,completionOutput,Fin.val_last] at hh
    omega
  have hf : lowTape k i ≠ completionFlag k := by
    intro he
    exact hi (congrArg Fin.val he)
  simp [resetWork,clearedWork,hnot,capturedWork,Function.update_of_ne ho,Function.update_of_ne hf]

theorem resetWork_parked {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp verdict : Tape) (bound : Nat) (answer : Prop)
    (hb : 1 ≤ bound) (hq : q.eval query.length = bound)
    (inner : Fin (7+(3+k)+1) → Tape)
    (h : clockedSATPost q k U base blocks query inp bound answer inp inner verdict) :
    ∀ i, Parked (resetWork inner verdict i) := by
  obtain ⟨hw,_,_⟩ := capturedWork_ready q U base blocks query inp verdict bound answer hb hq inner h
  intro i
  unfold resetWork clearedWork
  split
  · exact parkedInput_parked _
  · exact hw i

/-- The five registers to restore are still exact unary registers after scratch reset. -/
theorem resetWork_registers {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp verdict : Tape) (bound : Nat) (answer : Prop)
    (inner : Fin (7+(3+k)+1) → Tape)
    (h : clockedSATPost q k U base blocks query inp bound answer inp inner verdict) :
    resetWork inner verdict (lowTape k 1) = regTape (1+r) ∧
    resetWork inner verdict (lowTape k 2) = regTape r ∧
    resetWork inner verdict (lowTape k 7) = regTape query.length ∧
    resetWork inner verdict (lowTape k 8) = regTape (q.eval query.length) ∧
    resetWork inner verdict (lowTape k 9) = regTape (q.eval query.length) := by
  have h1 := bufferedWork_prefix q U base blocks query inp verdict bound answer inner h (1 : Fin 7)
  have h2 := bufferedWork_prefix q U base blocks query inp verdict bound answer inner h (2 : Fin 7)
  have h7 := bufferedWork_clock q U base blocks query inp verdict bound answer inner h (0 : Fin 3)
  have h8 := bufferedWork_clock q U base blocks query inp verdict bound answer inner h (1 : Fin 3)
  have h9 := bufferedWork_clock q U base blocks query inp verdict bound answer inner h (2 : Fin 3)
  change bufferedWork inner verdict (lowTape k 1) = regTape (1+r) at h1
  change bufferedWork inner verdict (lowTape k 2) = regTape r at h2
  change bufferedWork inner verdict (lowTape k 7) = regTape query.length at h7
  change bufferedWork inner verdict (lowTape k 8) = regTape (q.eval query.length) at h8
  change bufferedWork inner verdict (lowTape k 9) = regTape (q.eval query.length) at h9
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals rw [resetWork_low _ _ _ (by decide)]
  · rw [h1]; exact normalizeScratchHead_eq _ (parked_regTape _)
  · rw [h2]; exact normalizeScratchHead_eq _ (parked_regTape _)
  · rw [h7]; exact normalizeScratchHead_eq _ (parked_regTape _)
  · rw [h8]; exact normalizeScratchHead_eq _ (parked_regTape _)
  · rw [h9]; exact normalizeScratchHead_eq _ (parked_regTape _)

end IrrRAFEnumeration.CompletionQuery
