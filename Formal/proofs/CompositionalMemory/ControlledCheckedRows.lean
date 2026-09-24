import proofs.CompositionalMemory.ControlledLiteral

namespace CompositionalMemory.ControlledRows
open FiniteIntegerRows

theorem checked_literal_bounds (m : Nat) (hm : 0 < m) (v next : Array Int)
    (i : Nat) (hrow : rowOK m v next i=true) (g c : ℝ)
    (hg : 0 ≤ g) (hg1 : g ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    -(1/1000000 : ℝ) ≤ literal m v next i 0 g c ∧
    -(1/1000000 : ℝ) ≤ literal m v next i 1 g c ∧
    literal m v next i 2 g c ≤
      -(5/8 : ℝ)*(value v i 2 : ℝ)/(precisionScale : ℝ)+1/50000 := by
  have h := of_decide_eq_true hrow
  refine ⟨?_,?_,?_⟩
  · rw [literal_integer_identity m hm]
    exact controlled_return_bound m hm v next i 0 g c hg hg1 hc hc1 h.1
  · rw [literal_integer_identity m hm]
    exact controlled_return_bound m hm v next i 1 g c hg hg1 hc hc1 h.2.1
  · have ht := controlled_time_bound m hm v next i g c hg hg1 hc hc1 h.2.2.1
    rw [← literal_shifted_identity m hm] at ht
    ring_nf at ht ⊢
    linarith

theorem checked_value_upper (m : Nat) (v next : Array Int) (i : Nat)
    (hrow : rowOK m v next i=true) (col : Fin 2) :
    (value v i col.val : ℝ)/(precisionScale : ℝ) ≤ 1 := by
  have h := of_decide_eq_true hrow
  have hh : value v i col.val ≤ precisionScale := by
    fin_cases col
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
  apply (div_le_one (by norm_num [precisionScale])).mpr
  exact_mod_cast hh

theorem checked_time_lower (m : Nat) (v next : Array Int) (i : Nat)
    (hrow : rowOK m v next i=true) :
    1 ≤ (value v i 2 : ℝ)/(precisionScale : ℝ) := by
  have h := (of_decide_eq_true hrow).2.2.2.2.2
  apply (le_div_iff₀ (by norm_num [precisionScale])).mpr
  simpa using (show (precisionScale : ℝ) ≤ (value v i 2 : ℝ) by exact_mod_cast h)

theorem checked_birth_bound (N : Nat) (v : Array Int) (hb : birthOK N v=true)
    (i : Nat) (hi : i < stateCount N) (col : Fin 2)
    (hnew : newborn N col.val (i/(4*N+1)) (i%(4*N+1))) :
    (9951/10000 : ℝ) ≤ (value v i col.val : ℝ)/(precisionScale : ℝ)-
      (value v i 2 : ℝ)/(500000*(precisionScale : ℝ)) := by
  have h := of_decide_eq_true ((List.all_eq_true.mp hb) i (List.mem_range.mpr hi))
  have hh : 497550*precisionScale ≤ 500000*value v i col.val-value v i 2 := by
    fin_cases col
    · exact h.1 hnew
    · exact h.2 hnew
  have hr : (497550 : ℝ)*(precisionScale : ℝ) ≤
      500000*(value v i col.val : ℝ)-(value v i 2 : ℝ) := by exact_mod_cast hh
  norm_num [precisionScale] at hr ⊢
  linarith

end CompositionalMemory.ControlledRows
