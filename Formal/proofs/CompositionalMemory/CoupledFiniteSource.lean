import proofs.CompositionalMemory.ControlledRowTransport
import proofs.CompositionalMemory.CoupledDeadline

namespace CompositionalMemory
open FiniteCopy

/-- Two distinct resident modules share the same membrane layer. -/
abbrev CoupledLiveState (N : Nat) := Σ j : Fin (N+1),
  Fin 2 → Fin (16*(N+j.val)+1) × Fin (4*(N+j.val)+1)
abbrev CoupledFiniteState (N : Nat) := Option (CoupledLiveState N)
abbrev CoupledChannel := Fin 2 × Fin 8

def coupledClipped (N : Nat) (j : Fin (N+1)) (a : Fin 2 → Int × Int) :
    CoupledFiniteState N :=
  if h : ∀ k, 0 ≤ (a k).1 ∧ (a k).1 ≤ 16*((N : Int)+j.val) ∧
      0 ≤ (a k).2 ∧ (a k).2 ≤ 4*((N : Int)+j.val) then
    some ⟨j,fun k =>
      (⟨(a k).1.toNat,by have hk := h k; omega⟩,
       ⟨(a k).2.toNat,by have hk := h k; omega⟩)⟩
  else none

def coupledProposal (N : Nat) (s : CoupledLiveState N) (r : CoupledChannel) :
    Fin (N+1) × (Fin 2 → Int × Int) :=
  match s with
  | ⟨j,a⟩ =>
    let raw : Fin 2 → Int × Int := fun k => ((a k).1.val,(a k).2.val)
    if hj : j.val=N then (j,raw) else
    let x : Int := (a r.1).1.val
    let y : Int := (a r.1).2.val
    let changed := fun p => Function.update raw r.1 p
    if r.2.val=5 then
      if x=0 then (j,raw) else (⟨j.val+1,by omega⟩,changed (x-1,y))
    else if r.2.val=0 then (j,changed (x+1,y))
    else if r.2.val=1 then (j,changed (x+2,y-1))
    else if r.2.val=2 ∨ r.2.val=6 then (j,changed (x-1,y+1))
    else if r.2.val=7 then (j,changed (x+1,y-1))
    else (j,changed (x-1,y))

def coupledNext (N : Nat) (s : CoupledFiniteState N) (r : CoupledChannel) :
    CoupledFiniteState N :=
  match s with
  | none => none
  | some a => let p := coupledProposal N a r; coupledClipped N p.1 p.2

/-- Label-blind fixed rates; the last two channels are genuine symmetric
cross-catalysis by the other module's Y species. -/
noncomputable def coupledRate (N : Nat) (ε : ℝ)
    (s : CoupledFiniteState N) (r : CoupledChannel) : ℝ :=
  match s with
  | none => 0
  | some ⟨j,a⟩ =>
    if j.val=N then 0 else
    let x := (a r.1).1.val
    let y := (a r.1).2.val
    let other : Fin 2 := ⟨1-r.1.val,by omega⟩
    let z := (a other).2.val
    let m : ℝ := N+j.val
    ![40*m,1500*(y : ℝ),15*(x*(x-1) : Nat)/m,
      100*(x : ℝ)*(y : ℝ)/m,54*(x : ℝ),(x : ℝ)/10,
      ε*(x : ℝ)*(z : ℝ)/m,ε*(y : ℝ)*(z : ℝ)/m] r.2

theorem coupledRate_nonneg (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (s : CoupledFiniteState N) (r : CoupledChannel) : 0 ≤ coupledRate N ε s r := by
  cases s with
  | none => rfl
  | some s =>
    rcases s with ⟨j,a⟩
    by_cases hj : j.val=N
    · simp [coupledRate,hj]
    · rcases r with ⟨k,r⟩
      fin_cases r <;> norm_num [coupledRate,hj] <;> positivity

noncomputable def coupledFiniteModel (N : Nat) (ε : ℝ) (hε : 0 ≤ ε) :
    FiniteJumpModel (CoupledFiniteState N) CoupledChannel where
  next := coupledNext N
  rate := coupledRate N ε
  nonneg := coupledRate_nonneg N ε hε

end CompositionalMemory
