import proofs.CompositionalMemory.WideFiniteSource

namespace CompositionalMemory
open FiniteCopy FiniteIntegerRows
set_option maxHeartbeats 50000

theorem wideValue_clipped (data : Nat → Array Int) (col : Nat) (j : Fin 26) (x y : Int) :
    wideValue data col (wideClipped j x y) =
      (target (25+j.val) (data (25+j.val)) x y col 0 : ℝ)/(scale : ℝ) := by
  simp only [wideClipped,target,Nat.cast_add,Nat.cast_ofNat]
  split_ifs <;> simp [wideValue]

/-- Literal six-channel formula with a specified artificial-exit value. -/
noncomputable def wideLiteral (γ : ℝ) (m : Nat) (v next : Array Int) (i col : Nat)
    (outside : Int) : ℝ :=
  let x : Nat := i/(4*m+1)
  let y : Nat := i%(4*m+1)
  let z := (value v i col : ℝ)/(scale : ℝ)
  let t := fun a b => (target m v a b col outside : ℝ)/(scale : ℝ)
  40*(m : ℝ)*(t ((x : Int)+1) y-z)+
  1500*(y : ℝ)*(t ((x : Int)+2) ((y : Int)-1)-z)+
  15*(x : ℝ)*((x : ℝ)-1)/(m : ℝ)*(t ((x : Int)-1) ((y : Int)+1)-z)+
  100*(x : ℝ)*(y : ℝ)/(m : ℝ)*(t ((x : Int)-1) y-z)+
  54*(x : ℝ)*(t ((x : Int)-1) y-z)+
  γ*(x : ℝ)*((value next ((x-1)*(4*(m+1)+1)+y) col : ℝ)/(scale : ℝ)-z)

theorem wideLiteral_integer_identity (γ : ℝ) (m : Nat) (hm : 0 < m)
    (v next : Array Int) (i col : Nat) :
    wideLiteral γ m v next i col (if col=2 then scale else 0) =
      realResidual m v next i col γ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  dsimp [wideLiteral,realResidual,FiniteIntegerRows.residual,growthDifference]
  generalize hx : i/(4*m+1)=X
  generalize hy : i%(4*m+1)=Y
  have hXI : (i : Int)/(4*(m : Int)+1)=(X : Int) := by exact_mod_cast hx
  have hYI : (i : Int)%(4*(m : Int)+1)=(Y : Int) := by exact_mod_cast hy
  simp [hXI,hYI]
  dsimp [scale]
  field_simp
  ring

theorem wideLiteral_shifted_identity (γ : ℝ) (m : Nat) (hm : 0 < m)
    (v next : Array Int) (i col : Nat) :
    realResidual m v next i col γ+(5/8 : ℝ)*(value v i col : ℝ)/(scale : ℝ) =
      realShiftedResidual m v next i col γ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [realResidual,realShiftedResidual,shiftedResidual]
  push_cast
  norm_num [scale]
  field_simp
  ring

theorem wideClipped_self (j : Fin 26)
    (x : Fin (16*(25+j.val)+1)) (y : Fin (4*(25+j.val)+1)) :
    wideClipped j x.val y.val=some ⟨j,x,y⟩ := by
  have hx : (x.val : Int) ≤ 16*(25+(j.val : Int)) := by
    exact_mod_cast (Nat.le_of_lt_succ x.isLt)
  have hy : (y.val : Int) ≤ 4*(25+(j.val : Int)) := by
    exact_mod_cast (Nat.le_of_lt_succ y.isLt)
  simp [wideClipped,hx,hy]

theorem wideValue_growth (data : Nat → Array Int) (col : Nat) (j : Fin 26)
    (hj : j.val < 25) (x : Fin (16*(25+j.val)+1)) (y : Fin (4*(25+j.val)+1))
    (hx : 0 < x.val) :
    wideValue data col (wideClipped ⟨j.val+1,by omega⟩ ((x.val : Int)-1) y.val) =
      (value (data (25+j.val+1)) ((x.val-1)*(4*(25+j.val+1)+1)+y.val) col : ℝ)/
        (scale : ℝ) := by
  let j' : Fin 26 := ⟨j.val+1,by omega⟩
  let x' : Fin (16*(25+j'.val)+1) := ⟨x.val-1,by dsimp [j']; omega⟩
  let y' : Fin (4*(25+j'.val)+1) := ⟨y.val,by dsimp [j']; omega⟩
  have hc := wideClipped_self j' x' y'
  have hxc : (x'.val : Int)=(x.val : Int)-1 := by dsimp [x']; omega
  rw [hxc] at hc
  change wideValue data col (wideClipped j' ((x.val : Int)-1) y'.val)=_
  rw [hc]
  simp [wideValue,j',x',y',Nat.add_assoc]

theorem wide_index_coordinates (j : Fin 26)
    (x : Fin (16*(25+j.val)+1)) (y : Fin (4*(25+j.val)+1)) :
    (x.val*(4*(25+j.val)+1)+y.val)/(4*(25+j.val)+1)=x.val ∧
    (x.val*(4*(25+j.val)+1)+y.val)%(4*(25+j.val)+1)=y.val := by
  constructor
  · rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt y.isLt,zero_add]
  · rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt y.isLt]

theorem falling_count_cast (x : Nat) :
    ((x*(x-1) : Nat) : ℝ)=(x : ℝ)*((x : ℝ)-1) := by
  cases x with
  | zero => norm_num
  | succ n => simp [Nat.cast_mul,Nat.cast_add]

end CompositionalMemory
