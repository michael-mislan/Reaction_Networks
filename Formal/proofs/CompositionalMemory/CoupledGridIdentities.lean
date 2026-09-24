import proofs.CompositionalMemory.CoupledGeneratorEnvelope

namespace CompositionalMemory
open FiniteIntegerRows ControlledRows

theorem coupledGridValue_natural (m : Nat) (data : Nat → Array Int) (col x y : Nat)
    (hx : x ≤ 16*m) (hy : y ≤ 4*m) :
    coupledGridValue m data col x y=
      (value (data m) (x*(4*m+1)+y) col : ℝ)/(precisionScale : ℝ) := by
  have hx' : (x : Int) ≤ 16*(m : Int) := by exact_mod_cast hx
  have hy' : (y : Int) ≤ 4*(m : Int) := by exact_mod_cast hy
  simp [coupledGridValue,target,hx',hy']

theorem coupledGridValue_growth (m : Nat) (data : Nat → Array Int) (col x y : Nat)
    (hx : x ≤ 16*m) (hy : y ≤ 4*m) (hpos : 0 < x) :
    coupledGridValue (m+1) data col ((x : Int)-1) y=
      (value (data (m+1)) ((x-1)*(4*(m+1)+1)+y) col : ℝ)/(precisionScale : ℝ) := by
  have he : ((x-1 : Nat) : Int)=(x : Int)-1 := by omega
  rw [← he]
  exact coupledGridValue_natural (m+1) data col (x-1) y (by omega) (by omega)

theorem coupled_current_grid (N : Nat) (data : Nat → Array Int)
    (s : CoupledLiveState N) (k : Fin 2) (col : Nat) :
    coupledGridValue (N+s.1.val) data col (s.2 k).1.val (s.2 k).2.val=
      coupledCurrent N data s k col := by
  exact coupledGridValue_natural _ _ _ _ _
    (Nat.le_of_lt_succ (s.2 k).1.isLt) (Nat.le_of_lt_succ (s.2 k).2.isLt)

theorem coupled_index_coordinates (m : Nat) (x y : Nat) (hy : y ≤ 4*m) :
    (x*(4*m+1)+y)/(4*m+1)=x ∧ (x*(4*m+1)+y)%(4*m+1)=y := by
  constructor
  · rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt (by omega),zero_add]
  · rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (by omega)]

theorem coupled_control_ranges (m : Nat) (hm : 0 < m) (x y : Nat)
    (hx : x ≤ 16*m) (hy : y ≤ 4*m) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10) :
    0 ≤ (x : ℝ)/(16*(m : ℝ)) ∧ (x : ℝ)/(16*(m : ℝ)) ≤ 1 ∧
    0 ≤ 5*ε*(y : ℝ)/(2*(m : ℝ)) ∧ 5*ε*(y : ℝ)/(2*(m : ℝ)) ≤ 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx' : (x : ℝ) ≤ 16*(m : ℝ) := by exact_mod_cast hx
  have hy' : (y : ℝ) ≤ 4*(m : ℝ) := by exact_mod_cast hy
  refine ⟨by positivity,?_,by positivity,?_⟩
  · exact (div_le_one (by positivity)).mpr hx'
  · apply (div_le_one (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hε1 (show (0 : ℝ) ≤ y by positivity)]

end CompositionalMemory
