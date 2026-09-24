import proofs.CompositionalMemory.ReversibleRowTransport

namespace CompositionalMemory.ReversibleRows
open FiniteIntegerRows
set_option maxHeartbeats 120000

/-- Literal reversible resident rates plus the original shared growth and
cross-catalytic controls. Reverse growth is handled by an explicit monitor,
not silently included in this increasing-layer operator. -/
noncomputable def literal (m : Nat) (v next : Array Int) (i col : Nat)
    (g c : ℝ) : ℝ :=
  let x : Nat := i/(4*m+1)
  let y : Nat := i%(4*m+1)
  let z := (value v i col : ℝ)/(precisionScale : ℝ)
  let t := fun a b => (target m v a b col (if col=2 then precisionScale else 0) : ℝ)/
    (precisionScale : ℝ)-z
  (193/5)*(m : ℝ)*t ((x : Int)+1) y+
  1555*(y : ℝ)*t ((x : Int)+2) ((y : Int)-1)+
  15*(x : ℝ)*((x : ℝ)-1)/(m : ℝ)*t ((x : Int)-1) ((y : Int)+1)+
  100*(x : ℝ)*(y : ℝ)/(m : ℝ)*t ((x : Int)-1) y+
  (105/2)*(x : ℝ)*t ((x : Int)-1) y+
  (x : ℝ)/10*((value next ((x-1)*(4*(m+1)+1)+y) col : ℝ)/(precisionScale : ℝ)-z)+
  g*(8/5)*(m : ℝ)*((value next (x*(4*(m+1)+1)+y) col : ℝ)/(precisionScale : ℝ)-z)+
  c*(2/5)*((x : ℝ)*t ((x : Int)-1) ((y : Int)+1)+
    (y : ℝ)*t ((x : Int)+1) ((y : Int)-1))+
  (193/750000)*(x : ℝ)*t ((x : Int)-1) y+
  (311/30000)*(x : ℝ)*((x : ℝ)-1)/(m : ℝ)*t ((x : Int)-2) ((y : Int)+1)+
  15*(x : ℝ)*(y : ℝ)/(m : ℝ)*t ((x : Int)+1) ((y : Int)-1)+
  (1/1000)*(y : ℝ)*t ((x : Int)+1) y+
  (21/40000)*(m : ℝ)*t ((x : Int)+1) y

theorem literal_integer_identity (m : Nat) (hm : 0 < m)
    (v next : Array Int) (i col : Nat) (g c : ℝ) :
    literal m v next i col g c=controlledReturn m v next i col g c := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  dsimp [literal,controlledReturn,residuals]
  generalize hx : i/(4*m+1)=X
  generalize hy : i%(4*m+1)=Y
  have hXI : (i : Int)/(4*(m : Int)+1)=(X : Int) := by exact_mod_cast hx
  have hYI : (i : Int)%(4*(m : Int)+1)=(Y : Int) := by exact_mod_cast hy
  simp [hXI,hYI]
  dsimp [precisionScale,ControlledRows.precisionScale]
  field_simp
  ring

theorem literal_shifted_identity (m : Nat) (hm : 0 < m)
    (v next : Array Int) (i : Nat) (g c : ℝ) :
    literal m v next i 2 g c+(5/8 : ℝ)*(value v i 2 : ℝ)/(precisionScale : ℝ)=
      controlledTime m v next i g c := by
  rw [literal_integer_identity m hm]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [controlledReturn,controlledTime]
  norm_num [precisionScale,ControlledRows.precisionScale]
  field_simp
  ring

end CompositionalMemory.ReversibleRows
