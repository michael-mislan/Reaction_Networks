import proofs.IrrRAFEnumeration.SATRawIncidenceReusable
import proofs.IrrRAFEnumeration.SATLibraryAdapter

namespace IrrRAFEnumeration.SATSource

open Complexity SAT SATCompletion Complexity.TM

theorem incidenceCNFMatch_get (sign : Bool) (v j : Nat) (φ : CNF) (hj : j < φ.length) :
    incidenceCNFMatch sign v φ j = incidenceClauseMatch sign v φ[j] := by
  induction φ generalizing j with
  | nil => simp at hj
  | cons c cs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j (by simpa using hj)

theorem incidenceClauseMatch_mem (sign : Bool) (v : Nat) (c : Clause) :
    incidenceClauseMatch sign v c = decide (({sign := sign,var := v} : Lit) ∈ c) := by
  induction c with
  | nil => rfl
  | cons lit c ih =>
    change (((lit.sign == sign) && decide (lit.var = v)) || incidenceClauseMatch sign v c) = _
    rw [ih]
    cases lit with
    | mk a n =>
      cases a <;> cases sign <;> simp [List.mem_cons, Lit.mk.injEq, eq_comm]

theorem incidenceCNFMatch_libraryRect (φ : CNF) (N : Nat)
    (j : Fin φ.length) (x : Choice N) :
    incidenceCNFMatch x.2 x.1.val φ j.val = decide (x ∈ libraryRect φ N j) := by
  rw [incidenceCNFMatch_get x.2 x.1.val j.val φ j.isLt, incidenceClauseMatch_mem]
  simp only [mem_libraryRect]
  rfl

/-- Direct machine contract for an incidence cell of the existing padded
rectangle. This is the query used by row emission, not a semantic oracle. -/
theorem rawIncidenceReusableTM_libraryRect (φ : CNF) (N : Nat)
    (j : Fin φ.length) (x : Choice N) (inp : Tape) (ys : List Bool)
    (hin : inp.HasBinarySuffix φ.encode) (hhead : inp.head = 1) (hzero : inp.cells 0 = Γ.start) :
    (rawIncidenceReusableTM x.2).HoareTime
      (EmitPred inp (incidenceQueryWork j.val x.1.val) ys)
      (EmitPred inp (incidenceQueryWork j.val x.1.val) (ys ++ [decide (x ∈ libraryRect φ N j)]))
      (4*φ.encode.length+11) := by
  simpa only [incidenceCNFMatch_libraryRect φ N j x] using
    rawIncidenceReusableTM_correct x.2 x.1.val j.val φ inp ys hin hhead hzero

end IrrRAFEnumeration.SATSource
