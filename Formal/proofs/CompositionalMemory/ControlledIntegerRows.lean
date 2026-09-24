import proofs.CompositionalMemory.WideTerminalPayoff

namespace CompositionalMemory.ControlledRows
open FiniteIntegerRows

def precisionScale : Int := 4398046511104

structure Residuals where
  base : Int
  growth : Int
  cross : Int
  deriving Repr

/-- Common denominator10*m*precisionScale. The two controls are other-module
X/(16m) and the symmetric cross-catalytic activity divided by2/5. -/
def residuals (m : Nat) (v next : Array Int) (i col : Nat) : Residuals :=
  let xn := i/(4*m+1)
  let yn := i%(4*m+1)
  let x : Int := xn
  let y : Int := yn
  let z := value v i col
  let outside := if col=2 then precisionScale else 0
  let t := fun a b => target m v a b col outside-z
  let own := value next ((xn-1)*(4*(m+1)+1)+yn) col-z
  let shared := value next (xn*(4*(m+1)+1)+yn) col-z
  { base := 400*(m : Int)^2*t (x+1) y + 15000*(m : Int)*y*t (x+2) (y-1) +
      150*x*(x-1)*t (x-1) (y+1) + (1000*x*y+540*(m : Int)*x)*t (x-1) y +
      (m : Int)*x*own
    growth := 16*(m : Int)^2*shared
    cross := 4*(m : Int)*(x*t (x-1) (y+1)+y*t (x+1) (y-1)) }

def worstReturn (m : Nat) (v next : Array Int) (i col : Nat) : Int :=
  let r := residuals m v next i col
  r.base+min 0 r.growth+min 0 r.cross

def worstTime (m : Nat) (v next : Array Int) (i : Nat) : Int :=
  let r := residuals m v next i 2
  4*r.base+25*(m : Int)*value v i 2+max 0 (4*r.growth)+max 0 (4*r.cross)

/-- Residual budgets epsilon=1/10^6 and eta=1/50000. -/
def rowOK (m : Nat) (v next : Array Int) (i : Nat) : Bool := decide (
  -(10*(m : Int)*precisionScale) ≤ 1000000*worstReturn m v next i 0 ∧
  -(10*(m : Int)*precisionScale) ≤ 1000000*worstReturn m v next i 1 ∧
  50000*worstTime m v next i ≤ 40*(m : Int)*precisionScale ∧
  value v i 0 ≤ precisionScale ∧ value v i 1 ≤ precisionScale ∧ precisionScale ≤ value v i 2)

def checkLayer (m : Nat) (v next : Array Int) : Bool :=
  decide (v.size=3*stateCount m ∧ next.size=3*stateCount (m+1)) &&
    (List.range (stateCount m)).all (rowOK m v next)

def newborn (N col x y : Nat) : Prop :=
  (col=0 ∧ (N+9)/10 ≤ x ∧ x ≤ 2*N ∧ y ≤ 4*N/25) ∨
  (col=1 ∧ 7*N ≤ x ∧ x ≤ 14*N ∧ (N+9)/10 ≤ y ∧ y ≤ 25*N/10)

instance (N col x y : Nat) : Decidable (newborn N col x y) := by
  unfold newborn
  infer_instance

def birthOK (N : Nat) (v : Array Int) : Bool :=
  (List.range (stateCount N)).all fun i =>
    let x := i/(4*N+1)
    let y := i%(4*N+1)
    decide ((newborn N 0 x y →
      497550*precisionScale ≤ 500000*value v i 0-value v i 2) ∧
      (newborn N 1 x y →
      497550*precisionScale ≤ 500000*value v i 1-value v i 2))

def terminalRow (N : Nat) (v : Array Int) (i a b c d : Nat) : Bool :=
  let x := i/(8*N+1)
  let y := i%(8*N+1)
  decide (0 ≤ value v i 0 ∧ 0 ≤ value v i 1 ∧
    value v i 0*(2 : Int)^(x+y) ≤ precisionScale*(a : Int)*b ∧
    value v i 1*(2 : Int)^(x+y) ≤ precisionScale*(c : Int)*d ∧ value v i 2=precisionScale)

def terminalCheck (N : Nat) (v : Array Int) : Bool := Id.run do
  let px0 := (Array.range (32*N+1)).map fun x => splitNumerator x ((N+9)/10) (2*N)
  let py0 := (Array.range (8*N+1)).map fun y => splitNumerator y 0 (4*N/25)
  let px1 := (Array.range (32*N+1)).map fun x => splitNumerator x (7*N) (14*N)
  let py1 := (Array.range (8*N+1)).map fun y => splitNumerator y ((N+9)/10) (25*N/10)
  return decide (v.size=3*stateCount (2*N)) &&
    (List.range (stateCount (2*N))).all fun i =>
      terminalRow N v i px0[i/(8*N+1)]! py0[i%(8*N+1)]! px1[i/(8*N+1)]! py1[i%(8*N+1)]!

theorem checked_row (m : Nat) (v next : Array Int) (h : checkLayer m v next=true)
    (i : Nat) (hi : i < stateCount m) : rowOK m v next i=true := by
  have hall := (Bool.and_eq_true_iff.mp h).2
  exact (List.all_eq_true.mp hall) i (List.mem_range.mpr hi)

end CompositionalMemory.ControlledRows
