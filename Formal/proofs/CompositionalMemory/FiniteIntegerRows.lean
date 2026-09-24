import Mathlib

namespace CompositionalMemory.FiniteIntegerRows

/-- Parsing selects candidate integers; the checker validates those integers. -/
def unpack (s : String) : Array Int :=
  (s.splitOn ",").toArray.map String.toInt!

def scale : Int := 68719476736
def value (v : Array Int) (i col : Nat) : Int := v[i*3+col]!
def stateCount (m : Nat) : Nat := (16*m+1)*(4*m+1)

def target (m : Nat) (v : Array Int) (x y : Int) (col : Nat) (outside : Int) : Int :=
  if 0 ≤ x ∧ x ≤ 16*(m : Int) ∧ 0 ≤ y ∧ y ≤ 4*(m : Int)
  then value v (x.toNat*(4*m+1)+y.toNat) col else outside

/-- Exact generator residual with denominator 10*m*scale. The first two
columns are return values; the third is the time witness. -/
def residual (m : Nat) (v next : Array Int) (i col : Nat) : Int := Id.run do
  let x : Int := (i/(4*m+1) : Nat)
  let y : Int := (i%(4*m+1) : Nat)
  let z := value v i col
  let outside := if col=2 then scale else 0
  let future := value next ((x.toNat-1)*(4*(m+1)+1)+y.toNat) col
  return (m : Int)*x*(future-z)
    +400*(m : Int)^2*(target m v (x+1) y col outside-z)
    +15000*(m : Int)*y*(target m v (x+2) (y-1) col outside-z)
    +150*x*(x-1)*(target m v (x-1) (y+1) col outside-z)
    +1000*x*y*(target m v (x-1) y col outside-z)
    +540*(m : Int)*x*(target m v (x-1) y col outside-z)

def shiftedResidual (m : Nat) (v next : Array Int) (i col : Nat) : Int :=
  4*residual m v next i col+25*(m : Int)*value v i col

def growthDifference (m : Nat) (v next : Array Int) (i col : Nat) : Int :=
  let x : Int := (i/(4*m+1) : Nat)
  let y := i%(4*m+1)
  x*(value next ((x.toNat-1)*(4*(m+1)+1)+y) col-value v i col)

structure Limits where
  residual : Nat
  mgfResidual : Nat
  valueSensitivity : Nat
  mgfSensitivity : Nat
  deriving Repr

/-- These integer inequalities enclose the whole growth interval
1/10 +- 1/10^7 at epsilon=1/10000 and eta=1/4000. -/
def limitsOK (m : Nat) (lim : Limits) : Bool := decide (
  1000000*lim.residual+m*lim.valueSensitivity ≤ 1000*m*scale.toNat ∧
  250000*lim.mgfResidual+m*lim.mgfSensitivity ≤ 2500*m*scale.toNat)

def birthOK (v : Array Int) : Bool :=
  (List.range (stateCount 25)).all fun i =>
    let x := i/101
    let y := i%101
    decide ((3 ≤ x ∧ x ≤ 50 ∧ y ≤ 4 →
      248350*scale ≤ 250000*value v i 0-value v i 2) ∧
      (175 ≤ x ∧ x ≤ 350 ∧ 3 ≤ y ∧ y ≤ 62 →
      248350*scale ≤ 250000*value v i 1-value v i 2))

def rowOK (m : Nat) (v next : Array Int) (lim : Limits) (i : Nat) : Bool :=
  decide (
    (residual m v next i 0).natAbs ≤ lim.residual ∧
    (residual m v next i 1).natAbs ≤ lim.residual ∧
    (shiftedResidual m v next i 2).natAbs ≤ lim.mgfResidual ∧
    (growthDifference m v next i 0).natAbs ≤ lim.valueSensitivity ∧
    (growthDifference m v next i 1).natAbs ≤ lim.valueSensitivity ∧
    (growthDifference m v next i 2).natAbs ≤ lim.mgfSensitivity ∧
    value v i 0 ≤ scale ∧ value v i 1 ≤ scale ∧ scale ≤ value v i 2)

def checkLayer (m : Nat) (v next : Array Int) (lim : Limits) : Bool :=
  decide (v.size=3*stateCount m ∧ next.size=3*stateCount (m+1)) &&
    (List.range (stateCount m)).all (rowOK m v next lim)

theorem checked_row (m : Nat) (v next : Array Int) (lim : Limits)
    (h : checkLayer m v next lim=true) (i : Nat) (hi : i<stateCount m) :
    rowOK m v next lim i=true := by
  have hall := (Bool.and_eq_true_iff.mp h).2
  exact (List.all_eq_true.mp hall) i (List.mem_range.mpr hi)

end CompositionalMemory.FiniteIntegerRows
