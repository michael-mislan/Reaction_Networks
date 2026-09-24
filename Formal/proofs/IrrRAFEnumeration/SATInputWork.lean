import proofs.IrrRAFEnumeration.SATDirectQueries

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

def collectWork : List (Bool × Nat) → List Bool × Nat
  | [] => ([], 0)
  | p :: ps => let q := collectWork ps; (p.1 :: q.1, p.2+q.2)

theorem collectWork_value (xs : List (Bool × Nat)) :
    (collectWork xs).1 = xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons p ps ih => simp [collectWork, ih]

theorem collectWork_bound (xs : List (Bool × Nat)) (B : Nat)
    (h : ∀ p ∈ xs, p.2 ≤ B) : (collectWork xs).2 ≤ xs.length*B := by
  induction xs with
  | nil => simp [collectWork]
  | cons p ps ih =>
      have hp := h p (by simp)
      have ht := ih (fun q hq => h q (by simp [hq]))
      simp only [collectWork, List.length_cons]
      nlinarith

def sourceTableWork (n m : Nat) (body : List Bool) : List (Bool × Nat) :=
  List.ofFn (fun i => datumWork (clauseWork n m body)
    ((slotCode (moleculeCount n m) (reactionCount n m)).symm i))

def directSourceWork (n m : Nat) (body : List Bool) : List Bool × Nat :=
  let p := collectWork (sourceTableWork n m body)
  (List.replicate (moleculeCount n m) true ++ [false] ++
    List.replicate (reactionCount n m) true ++ [false] ++ p.1, p.2)

theorem directSourceWork_value (n m : Nat) (body : List Bool) :
    (directSourceWork n m body).1 = sourceBits (decodeClauses n m body) := by
  simp only [directSourceWork, collectWork_value, sourceTableWork, List.map_ofFn,
    sourceBits, sourceBody]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact datumWork_correct _ _ (clauseWork_value n m body) _

theorem directSourceWork_cost (n m : Nat) (body : List Bool) :
    (directSourceWork n m body).2 ≤ 500*(n+m+1)^4*(body.length+1) := by
  have hb := collectWork_bound (sourceTableWork n m body) (body.length+1) (by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact datumWork_cost body _)
  have hlen : (sourceTableWork n m body).length ≤
      (sourceBits (decodeClauses n m body)).length := by
    simp only [sourceTableWork, List.length_ofFn, sourceBits_length]
    omega
  exact hb.trans (Nat.mul_le_mul_right _
    (hlen.trans (sourceBits_polynomial (decodeClauses n m body))))

theorem readUnary_budget (bits : List Bool) :
    (readUnary bits).1 + (readUnary bits).2.length ≤ bits.length := by
  induction bits with
  | nil => simp [readUnary]
  | cons b bs ih =>
      cases b with
      | false => simp [readUnary]
      | true => simp only [readUnary, List.length_cons]; omega

theorem decodeHeader_budget (bits : List Bool) :
    (decodeHeader bits).1 + (decodeHeader bits).2.1 +
      (decodeHeader bits).2.2.length ≤ bits.length := by
  have ha := readUnary_budget bits
  have hb := readUnary_budget (readUnary bits).2
  dsimp only [decodeHeader]
  omega

/-- The instrumented compiler records all CNF-body list inspections. -/
def directCompileWork (bits : List Bool) : List Bool × Nat :=
  let p := decodeHeader bits
  directSourceWork p.1 p.2.1 p.2.2

theorem directCompileWork_value (bits : List Bool) :
    (directCompileWork bits).1 = compileCNF bits := by
  exact directSourceWork_value _ _ _

/-- A genuine bound on executed input-list traversal for every bitstring.
Arithmetic, parsing and allocations still require their separate step analysis. -/
theorem directCompileWork_input_bound (bits : List Bool) :
    (directCompileWork bits).2 ≤ 500*(bits.length+1)^5 := by
  have hp := decodeHeader_budget bits
  have hsize : (decodeHeader bits).1+(decodeHeader bits).2.1+1 ≤ bits.length+1 := by omega
  have hbody : (decodeHeader bits).2.2.length+1 ≤ bits.length+1 := by omega
  have h := directSourceWork_cost (decodeHeader bits).1 (decodeHeader bits).2.1
    (decodeHeader bits).2.2
  apply h.trans
  calc
    _ ≤ (500*(bits.length+1)^4)*(bits.length+1) := Nat.mul_le_mul
      (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hsize 4)) hbody
    _ = _ := by ring

end IrrRAFEnumeration.SATSource
