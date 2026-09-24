import proofs.CompositionalMemory.CoupledFiniteSource
import proofs.CompositionalMemory.ReversibleLiteral

namespace CompositionalMemory
open FiniteCopy

abbrev ReversibleChannel := Fin 2 × Fin 13

/-- The first eight channels retain the forward/shared-growth proposal map.
The remaining five are the resident reverse reactions. -/
def reversibleProposal (N : Nat) (s : CoupledLiveState N) (r : ReversibleChannel) :
    Fin (N+1) × (Fin 2 → Int × Int) :=
  if hr : r.2.val<8 then coupledProposal N s (r.1,⟨r.2.val,hr⟩) else
  match s with
  | ⟨j,a⟩ =>
    let raw : Fin 2 → Int × Int := fun k => ((a k).1.val,(a k).2.val)
    if j.val=N then (j,raw) else
    let x : Int := (a r.1).1.val
    let y : Int := (a r.1).2.val
    let changed := fun p => Function.update raw r.1 p
    if r.2.val=8 then (j,changed (x-1,y))
    else if r.2.val=9 then (j,changed (x-2,y+1))
    else if r.2.val=10 then (j,changed (x+1,y-1))
    else (j,changed (x+1,y))

def reversibleNext (N : Nat) (s : CoupledFiniteState N) (r : ReversibleChannel) :
    CoupledFiniteState N :=
  match s with
  | none => none
  | some a => let p := reversibleProposal N a r; coupledClipped N p.1 p.2

/-- Fixed retuned reversible kinetics; word labels do not enter the rates.
Reverse growth is a separate monitored perturbation of this layer model. -/
noncomputable def reversibleRate (N : Nat) (ε : ℝ)
    (s : CoupledFiniteState N) (r : ReversibleChannel) : ℝ :=
  match s with
  | none => 0
  | some ⟨j,a⟩ =>
    if j.val=N then 0 else
    let x := (a r.1).1.val
    let y := (a r.1).2.val
    let other : Fin 2 := ⟨1-r.1.val,by omega⟩
    let z := (a other).2.val
    let m : ℝ := N+j.val
    ![(193/5)*m,1555*(y : ℝ),15*(x*(x-1) : Nat)/m,
      100*(x : ℝ)*(y : ℝ)/m,(105/2)*(x : ℝ),(x : ℝ)/10,
      ε*(x : ℝ)*(z : ℝ)/m,ε*(y : ℝ)*(z : ℝ)/m,
      (193/750000)*(x : ℝ),(311/30000)*(x*(x-1) : Nat)/m,
      15*(x : ℝ)*(y : ℝ)/m,(1/1000)*(y : ℝ),(21/40000)*m] r.2

theorem reversibleRate_nonneg (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (s : CoupledFiniteState N) (r : ReversibleChannel) : 0 ≤ reversibleRate N ε s r := by
  cases s with
  | none => rfl
  | some s =>
    rcases s with ⟨j,a⟩
    by_cases hj : j.val=N
    · simp [reversibleRate,hj]
    · rcases r with ⟨k,r⟩
      fin_cases r <;> norm_num [reversibleRate,hj] <;> positivity

noncomputable def reversibleFiniteModel (N : Nat) (ε : ℝ) (hε : 0 ≤ ε) :
    FiniteJumpModel (CoupledFiniteState N) ReversibleChannel where
  next := reversibleNext N
  rate := reversibleRate N ε
  nonneg := reversibleRate_nonneg N ε hε

end CompositionalMemory
