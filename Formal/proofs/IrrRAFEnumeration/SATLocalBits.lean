import proofs.IrrRAFEnumeration.SATUniformCompiler

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

/-- Direct signal-input test: no finite set is constructed. -/
def needBit {n m : Nat} : Step n m → Wire n m → Bool
  | .conflict i, .literal x => decide (x.1 = i)
  | .coverage x, .literal y => decide (y = x)
  | .clause _ x, .literal y => decide (y = x)
  | .finish, .covered _ => true
  | .finish, .clause _ => true
  | _, _ => false

/-- Only the clause-output case queries the supplied incidence function. -/
def produceBit {n m : Nat} (hit : Fin m → Choice n → Bool) :
    Step n m → Wire n m → Bool
  | .conflict _, .output => true
  | .coverage x, .covered i => decide (i = x.1)
  | .clause j x, .clause k => if k = j then hit j x else false
  | .finish, .output => true
  | _, _ => false

theorem needBit_correct {n m : Nat} (s : Step n m) (v : Wire n m) :
    needBit s v = true ↔ v ∈ needs s := by
  cases s <;> cases v <;> simp [needBit, needs]
  rename_i i x
  rcases x with ⟨k,b⟩
  cases b <;> simp

theorem produceBit_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (s : Step n m) (v : Wire n m) :
    produceBit (fun j x => decide (x ∈ Φ j)) s v = true ↔ v ∈ produces Φ s := by
  cases s <;> cases v <;> simp [produceBit, produces]
  all_goals split_ifs <;> simp_all

/-- Executable list lookup with the number of inspected list constructors.
The empty-list/default case also costs one inspection. -/
def readBitWork : List Bool → Nat → Bool × Nat
  | [], _ => (false, 1)
  | b :: _, 0 => (b, 1)
  | _ :: bs, k+1 => let p := readBitWork bs k; (p.1, p.2+1)

theorem readBitWork_value (bs : List Bool) (k : Nat) :
    (readBitWork bs k).1 = bs.getD k false := by
  induction bs generalizing k with
  | nil => simp [readBitWork]
  | cons b bs ih => cases k <;> simp [readBitWork, ih]

theorem readBitWork_cost (bs : List Bool) (k : Nat) :
    (readBitWork bs k).2 ≤ bs.length+1 := by
  induction bs generalizing k with
  | nil => simp [readBitWork]
  | cons b bs ih =>
      cases k with
      | zero => simp [readBitWork]
      | succ k => simpa [readBitWork] using Nat.add_le_add_right (ih k) 1

/-- Instrument exactly the input-list traversal performed by a clause lookup. -/
def clauseWork (n m : Nat) (body : List Bool) (j : Fin m) (x : Choice n) : Bool × Nat :=
  readBitWork body (finProdFinEquiv (j, choiceOffset n x)).val

theorem clauseWork_value (n m : Nat) (body : List Bool) (j : Fin m) (x : Choice n) :
    (clauseWork n m body j x).1 = true ↔ x ∈ decodeClauses n m body j := by
  simp [clauseWork, readBitWork_value, decodeClauses]

def produceWork {n m : Nat} (hit : Fin m → Choice n → Bool × Nat) :
    Step n m → Wire n m → Bool × Nat
  | .clause j x, .clause k => if k = j then hit j x else (false, 0)
  | s, v => (produceBit (fun _ _ => false) s v, 0)

theorem produceWork_value {n m : Nat} (hit : Fin m → Choice n → Bool × Nat)
    (s : Step n m) (v : Wire n m) :
    (produceWork hit s v).1 = produceBit (fun j x => (hit j x).1) s v := by
  cases s <;> cases v <;> simp [produceWork, produceBit]
  split_ifs <;> simp_all

theorem produceWork_cost {n m : Nat} (hit : Fin m → Choice n → Bool × Nat)
    (B : Nat) (h : ∀ j x, (hit j x).2 ≤ B) (s : Step n m) (v : Wire n m) :
    (produceWork hit s v).2 ≤ B := by
  cases s <;> cases v <;> simp [produceWork]
  split_ifs
  · exact h _ _
  · exact Nat.zero_le _

/-- A local source output query inspects at most L+1 input-list constructors.
This bound counts input traversal, not yet all arithmetic or machine steps. -/
theorem local_output_query_bound {n m : Nat} (body : List Bool)
    (s : Step n m) (v : Wire n m) :
    (produceWork (clauseWork n m body) s v).2 ≤ body.length+1 :=
  produceWork_cost _ _ (fun _ _ => readBitWork_cost _ _) s v

end IrrRAFEnumeration.SATSource
