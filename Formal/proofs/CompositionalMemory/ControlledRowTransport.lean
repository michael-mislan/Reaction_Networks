import proofs.CompositionalMemory.ControlledIntegerRows

namespace CompositionalMemory.ControlledRows
open FiniteIntegerRows
attribute [local irreducible] residuals worstReturn worstTime

theorem min_le_control (a t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    min 0 a ≤ t*a := by
  by_cases ha : 0 ≤ a
  · rw [min_eq_left ha]
    exact mul_nonneg ht ha
  · rw [min_eq_right (le_of_not_ge ha)]
    nlinarith

theorem control_le_max (a t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t*a ≤ max 0 a := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_right ha]
    nlinarith
  · rw [max_eq_left (le_of_not_ge ha)]
    exact mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_ge ha)

noncomputable def controlledReturn (m : Nat) (v next : Array Int) (i col : Nat)
    (g c : ℝ) : ℝ :=
  let r := residuals m v next i col
  ((r.base : ℝ)+g*r.growth+c*r.cross)/(10*(m : ℝ)*(precisionScale : ℝ))

noncomputable def controlledTime (m : Nat) (v next : Array Int) (i : Nat)
    (g c : ℝ) : ℝ :=
  let r := residuals m v next i 2
  (4*(r.base : ℝ)+25*(m : ℝ)*value v i 2+g*(4*r.growth)+c*(4*r.cross))/
    (40*(m : ℝ)*(precisionScale : ℝ))

theorem controlled_return_bound (m : Nat) (hm : 0 < m) (v next : Array Int)
    (i col : Nat) (g c : ℝ) (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (h : -(10*(m : Int)*precisionScale) ≤ 1000000*worstReturn m v next i col) :
    -(1/1000000 : ℝ) ≤ controlledReturn m v next i col g c := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD : (0 : ℝ) < 10*(m : ℝ)*(precisionScale : ℝ) := by
    norm_num [precisionScale]; positivity
  have hh : -(10*(m : ℝ)*(precisionScale : ℝ)) ≤
      1000000*(worstReturn m v next i col : ℝ) := by exact_mod_cast h
  have hg' := min_le_control ((residuals m v next i col).growth : ℝ) g hg hg1
  have hc' := min_le_control ((residuals m v next i col).cross : ℝ) c hc hc1
  simp only [worstReturn, Int.cast_add, Int.cast_min, Int.cast_zero] at hh
  unfold controlledReturn
  apply (le_div_iff₀ hD).mpr
  nlinarith only [hh,hg',hc']

theorem controlled_time_bound (m : Nat) (hm : 0 < m) (v next : Array Int)
    (i : Nat) (g c : ℝ) (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (h : 50000*worstTime m v next i ≤ 40*(m : Int)*precisionScale) :
    controlledTime m v next i g c ≤ (1/50000 : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD : (0 : ℝ) < 40*(m : ℝ)*(precisionScale : ℝ) := by
    norm_num [precisionScale]; positivity
  have hh : 50000*(worstTime m v next i : ℝ) ≤
      40*(m : ℝ)*(precisionScale : ℝ) := by exact_mod_cast h
  have hg' := control_le_max (4*((residuals m v next i 2).growth : ℝ)) g hg hg1
  have hc' := control_le_max (4*((residuals m v next i 2).cross : ℝ)) c hc hc1
  simp only [worstTime, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    Int.cast_natCast, Int.cast_max, Int.cast_zero] at hh
  unfold controlledTime
  apply (div_le_iff₀ hD).mpr
  nlinarith only [hh,hg',hc']

end CompositionalMemory.ControlledRows
