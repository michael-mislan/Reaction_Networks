import proofs.CompositionalMemory.ControlledIntegerRows

namespace CompositionalMemory.ReversibleRows
open FiniteIntegerRows

def precisionScale : Int := ControlledRows.precisionScale
def rateDenominator : Int := 3000000

/-- Exact retuned reversible resident generator, denominator3,000,000*m*S.
The rate table is fixed across words. Other-module growth and symmetric
cross-catalysis remain the same two affine controls as in the forward model. -/
def residuals (m : Nat) (v next : Array Int) (i col : Nat) : ControlledRows.Residuals :=
  let xn := i/(4*m+1)
  let yn := i%(4*m+1)
  let x : Int := xn
  let y : Int := yn
  let z := value v i col
  let outside := if col=2 then precisionScale else 0
  let t := fun a b => target m v a b col outside-z
  let own := value next ((xn-1)*(4*(m+1)+1)+yn) col-z
  let shared := value next (xn*(4*(m+1)+1)+yn) col-z
  { base := (115801575*(m : Int)^2+3000*(m : Int)*y)*t (x+1) y +
      4665000000*(m : Int)*y*t (x+2) (y-1) +
      45000000*x*(x-1)*t (x-1) (y+1) +
      (300000000*x*y+157500772*(m : Int)*x)*t (x-1) y +
      300000*(m : Int)*x*own + 31100*x*(x-1)*t (x-2) (y+1) +
      45000000*x*y*t (x+1) (y-1)
    growth := 4800000*(m : Int)^2*shared
    cross := 1200000*(m : Int)*(x*t (x-1) (y+1)+y*t (x+1) (y-1)) }

def worstReturn (m : Nat) (v next : Array Int) (i col : Nat) : Int :=
  let r := residuals m v next i col
  r.base+min 0 r.growth+min 0 r.cross

def worstTime (m : Nat) (v next : Array Int) (i : Nat) : Int :=
  let r := residuals m v next i 2
  8*r.base+15000000*(m : Int)*value v i 2+max 0 (8*r.growth)+max 0 (8*r.cross)

def rowOK (m : Nat) (v next : Array Int) (i : Nat) : Bool := decide (
  -(rateDenominator*(m : Int)*precisionScale) ≤ 1000000*worstReturn m v next i 0 ∧
  -(rateDenominator*(m : Int)*precisionScale) ≤ 1000000*worstReturn m v next i 1 ∧
  50000*worstTime m v next i ≤ 8*rateDenominator*(m : Int)*precisionScale ∧
  value v i 0 ≤ precisionScale ∧ value v i 1 ≤ precisionScale ∧ precisionScale ≤ value v i 2)

def checkLayer (m : Nat) (v next : Array Int) : Bool :=
  decide (v.size=3*stateCount m ∧ next.size=3*stateCount (m+1)) &&
    (List.range (stateCount m)).all (rowOK m v next)

/-- The stronger birth threshold0.99555 leaves room for reverse-growth and
finite-supply costs after the basic two-module deadline bound0.991. -/
def birthOK (N : Nat) (v : Array Int) : Bool :=
  (List.range (stateCount N)).all fun i =>
    let x := i/(4*N+1)
    let y := i%(4*N+1)
    decide ((ControlledRows.newborn N 0 x y →
      497775*precisionScale ≤ 500000*value v i 0-value v i 2) ∧
      (ControlledRows.newborn N 1 x y →
      497775*precisionScale ≤ 500000*value v i 1-value v i 2))

def terminalCheck (N : Nat) (v : Array Int) : Bool := ControlledRows.terminalCheck N v

theorem checked_row (m : Nat) (v next : Array Int) (h : checkLayer m v next=true)
    (i : Nat) (hi : i < stateCount m) : rowOK m v next i=true := by
  have hall := (Bool.and_eq_true_iff.mp h).2
  exact (List.all_eq_true.mp hall) i (List.mem_range.mpr hi)

end CompositionalMemory.ReversibleRows
