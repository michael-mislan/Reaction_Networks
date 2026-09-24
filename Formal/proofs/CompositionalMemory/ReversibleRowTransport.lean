import proofs.CompositionalMemory.ReversibleIntegerRows
import proofs.CompositionalMemory.ControlledRowTransport

namespace CompositionalMemory.ReversibleRows
open FiniteIntegerRows
attribute [local irreducible] residuals worstReturn worstTime

noncomputable def controlledReturn (m : Nat) (v next : Array Int) (i col : Nat)
    (g c : ℝ) : ℝ :=
  let r := residuals m v next i col
  ((r.base : ℝ)+g*r.growth+c*r.cross)/(3000000*(m : ℝ)*(precisionScale : ℝ))

noncomputable def controlledTime (m : Nat) (v next : Array Int) (i : Nat)
    (g c : ℝ) : ℝ :=
  let r := residuals m v next i 2
  (8*(r.base : ℝ)+15000000*(m : ℝ)*value v i 2+g*(8*r.growth)+c*(8*r.cross))/
    (24000000*(m : ℝ)*(precisionScale : ℝ))

theorem controlled_return_bound (m : Nat) (hm : 0 < m) (v next : Array Int)
    (i col : Nat) (g c : ℝ) (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (h : -(rateDenominator*(m : Int)*precisionScale) ≤ 1000000*worstReturn m v next i col) :
    -(1/1000000 : ℝ) ≤ controlledReturn m v next i col g c := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD : (0 : ℝ) < 3000000*(m : ℝ)*(precisionScale : ℝ) := by
    norm_num [precisionScale,ControlledRows.precisionScale]; positivity
  have hh : -(3000000*(m : ℝ)*(precisionScale : ℝ)) ≤
      1000000*(worstReturn m v next i col : ℝ) := by
    norm_num only [rateDenominator] at h
    exact_mod_cast h
  have hg' := ControlledRows.min_le_control ((residuals m v next i col).growth : ℝ) g hg hg1
  have hc' := ControlledRows.min_le_control ((residuals m v next i col).cross : ℝ) c hc hc1
  simp only [worstReturn,Int.cast_add,Int.cast_min,Int.cast_zero] at hh
  unfold controlledReturn
  apply (le_div_iff₀ hD).mpr
  nlinarith only [hh,hg',hc']

theorem controlled_time_bound (m : Nat) (hm : 0 < m) (v next : Array Int)
    (i : Nat) (g c : ℝ) (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (h : 50000*worstTime m v next i ≤ 8*rateDenominator*(m : Int)*precisionScale) :
    controlledTime m v next i g c ≤ (1/50000 : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD : (0 : ℝ) < 24000000*(m : ℝ)*(precisionScale : ℝ) := by
    norm_num [precisionScale,ControlledRows.precisionScale]; positivity
  have hh : 50000*(worstTime m v next i : ℝ) ≤
      24000000*(m : ℝ)*(precisionScale : ℝ) := by
    norm_num only [rateDenominator] at h
    exact_mod_cast h
  have hg' := ControlledRows.control_le_max (8*((residuals m v next i 2).growth : ℝ)) g hg hg1
  have hc' := ControlledRows.control_le_max (8*((residuals m v next i 2).cross : ℝ)) c hc hc1
  simp only [worstTime,Int.cast_add,Int.cast_mul,Int.cast_ofNat,
    Int.cast_natCast,Int.cast_max,Int.cast_zero] at hh
  unfold controlledTime
  apply (div_le_iff₀ hD).mpr
  nlinarith only [hh,hg',hc']

end CompositionalMemory.ReversibleRows
