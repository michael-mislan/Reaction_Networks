import proofs.CompositionalMemory.FiniteIntegerRows

namespace CompositionalMemory.FiniteIntegerRows

/-- Number of fair molecule assignments for which both complementary counts
lie in the same integer interval. -/
def splitNumerator (n lo hi : Nat) : Nat :=
  ∑ k ∈ Finset.range (n+1),
    if lo ≤ k ∧ k ≤ hi ∧ lo ≤ n-k ∧ n-k ≤ hi then n.choose k else 0

noncomputable def exactTerminalReward (x y label : Nat) : ℝ :=
  if label=0 then
    (splitNumerator x 3 50 : ℝ)*(splitNumerator y 0 4 : ℝ)/2^(x+y)
  else
    (splitNumerator x 175 350 : ℝ)*(splitNumerator y 3 62 : ℝ)/2^(x+y)

def terminalRow (v : Array Int) (i a b c d : Nat) : Bool :=
  let x := i/201
  let y := i%201
  decide (0 ≤ value v i 0 ∧ 0 ≤ value v i 1 ∧
    value v i 0*(2 : Int)^(x+y) ≤ scale*(a : Int)*b ∧
    value v i 1*(2 : Int)^(x+y) ≤ scale*(c : Int)*d ∧
    value v i 2=scale)

/-- Axis sums are evaluated once per count, rather than once per pair. -/
def terminalCheck (v : Array Int) : Bool := Id.run do
  let px0 := (Array.range 801).map fun x => splitNumerator x 3 50
  let py0 := (Array.range 201).map fun y => splitNumerator y 0 4
  let px1 := (Array.range 801).map fun x => splitNumerator x 175 350
  let py1 := (Array.range 201).map fun y => splitNumerator y 3 62
  return decide (v.size=3*stateCount 50) &&
    (List.range (stateCount 50)).all fun i =>
      terminalRow v i px0[i/201]! py0[i%201]! px1[i/201]! py1[i%201]!

end CompositionalMemory.FiniteIntegerRows
