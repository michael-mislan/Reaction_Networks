import proofs.CompositionalMemory.FiniteRowTransport
import proofs.CompositionalMemory.FiniteDeadlineCertificate

namespace CompositionalMemory
open FiniteCopy

/-- Layer0 is membrane25; layer25 is the absorbing division membrane50. -/
abbrev WideLiveState := Σ j : Fin 26,
  Fin (16*(25+j.val)+1) × Fin (4*(25+j.val)+1)

/-- `none` is artificial truncation failure, never a successful division. -/
abbrev WideFiniteState := Option WideLiveState

def wideClipped (j : Fin 26) (x y : Int) : WideFiniteState :=
  if h : 0 ≤ x ∧ x ≤ 16*(25+(j.val : Int)) ∧
      0 ≤ y ∧ y ≤ 4*(25+(j.val : Int)) then
    some ⟨j,⟨x.toNat,by omega⟩,⟨y.toNat,by omega⟩⟩
  else none

def wideNext (s : WideFiniteState) (r : Fin 6) : WideFiniteState :=
  match s with
  | none => none
  | some ⟨j,x,y⟩ =>
    if hj : j.val=25 then s else
    if r.val=5 then
      if x.val=0 then s else
        wideClipped ⟨j.val+1,by omega⟩ ((x.val : Int)-1) y.val
    else if r.val=0 then wideClipped j ((x.val : Int)+1) y.val
    else if r.val=1 then wideClipped j ((x.val : Int)+2) ((y.val : Int)-1)
    else if r.val=2 then wideClipped j ((x.val : Int)-1) ((y.val : Int)+1)
    else wideClipped j ((x.val : Int)-1) y.val

noncomputable def wideRate (γ : ℝ) (s : WideFiniteState) (r : Fin 6) : ℝ :=
  match s with
  | none => 0
  | some ⟨j,x,y⟩ =>
    if j.val=25 then 0 else
    ![40*(25+(j.val : ℝ)),1500*(y.val : ℝ),
      15*(x.val*(x.val-1) : Nat)/(25+(j.val : ℝ)),
      100*(x.val : ℝ)*(y.val : ℝ)/(25+(j.val : ℝ)),
      54*(x.val : ℝ),γ*(x.val : ℝ)] r

theorem wideRate_nonneg (γ : ℝ) (hγ : 0 ≤ γ) (s : WideFiniteState) (r : Fin 6) :
    0 ≤ wideRate γ s r := by
  cases s with
  | none => rfl
  | some s =>
    rcases s with ⟨j,x,y⟩
    by_cases hj : j.val=25
    · simp [wideRate,hj]
    · fin_cases r <;> norm_num [wideRate,hj] <;> positivity

noncomputable def wideFiniteModel (γ : ℝ) (hγ : 0 ≤ γ) :
    FiniteJumpModel WideFiniteState (Fin 6) where
  next := wideNext
  rate := wideRate γ
  nonneg := wideRate_nonneg γ hγ

noncomputable def wideValue (data : Nat → Array Int) (col : Nat) : WideFiniteState → ℝ
  | none => 0
  | some ⟨j,x,y⟩ =>
    (FiniteIntegerRows.value (data (25+j.val))
      (x.val*(4*(25+j.val)+1)+y.val) col : ℝ)/(FiniteIntegerRows.scale : ℝ)

noncomputable def wideTimeWitness (data : Nat → Array Int) : WideFiniteState → ℝ
  | none => 0
  | some ⟨j,x,y⟩ => if j.val=25 then 0 else wideValue data 2 (some ⟨j,x,y⟩)

noncomputable def wideTerminalPayoff (data : Nat → Array Int) (col : Nat) : WideFiniteState → ℝ
  | none => 0
  | some ⟨j,x,y⟩ => if j.val=25 then wideValue data col (some ⟨j,x,y⟩) else 0

theorem wide_failure_absorbing (γ : ℝ) (hγ : 0 ≤ γ) (f : WideFiniteState → ℝ) :
    (wideFiniteModel γ hγ).generator f none=0 := by
  simp [FiniteJumpModel.generator,wideFiniteModel,wideRate]

theorem wide_division_absorbing (γ : ℝ) (hγ : 0 ≤ γ) (f : WideFiniteState → ℝ)
    (j : Fin 26) (hj : j.val=25)
    (x : Fin (16*(25+j.val)+1)) (y : Fin (4*(25+j.val)+1)) :
    (wideFiniteModel γ hγ).generator f (some ⟨j,x,y⟩)=0 := by
  simp [FiniteJumpModel.generator,wideFiniteModel,wideRate,hj]

end CompositionalMemory
