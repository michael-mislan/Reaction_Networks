import proofs.CompositionalMemory.WideCheckedDeadline

namespace CompositionalMemory
open FiniteIntegerRows
set_option maxHeartbeats 40000

def wideNewborn (col x y : Nat) : Prop :=
  (col=0 ∧ 3 ≤ x ∧ x ≤ 50 ∧ y ≤ 4) ∨
  (col=1 ∧ 175 ≤ x ∧ x ≤ 350 ∧ 3 ≤ y ∧ y ≤ 62)

theorem wide_newborn_count_bound (col x y : Nat) (h : wideNewborn col x y) :
    x+y ≤ 412 ∧ x < 401 ∧ y < 101 ∧ (col=0 ∨ col=1) := by
  unfold wideNewborn at h
  omega

theorem checked_birth_fraction (v : Array Int) (h : birthOK v=true)
    (col x y : Nat) (hb : wideNewborn col x y) :
    (248350 : ℝ) ≤
      250000*((value v (x*101+y) col : ℝ)/(scale : ℝ))-
        (value v (x*101+y) 2 : ℝ)/(scale : ℝ) := by
  have hc := wide_newborn_count_bound col x y hb
  have hi : x*101+y < stateCount 25 := by norm_num [stateCount]; omega
  have hx : (x*101+y)/101=x := by omega
  have hy : (x*101+y)%101=y := by omega
  have hh := of_decide_eq_true ((List.all_eq_true.mp h) (x*101+y) (List.mem_range.mpr hi))
  rw [hx,hy] at hh
  have hz : 248350*scale ≤ 250000*value v (x*101+y) col-value v (x*101+y) 2 := by
    rcases hb with ⟨rfl,hx0,hx1,hy1⟩ | ⟨rfl,hx0,hx1,hy0,hy1⟩
    · exact hh.1 ⟨hx0,hx1,hy1⟩
    · exact hh.2 ⟨hx0,hx1,hy0,hy1⟩
  have hr : (248350 : ℝ)*(scale : ℝ) ≤
      250000*(value v (x*101+y) col : ℝ)-(value v (x*101+y) 2 : ℝ) := by
    exact_mod_cast hz
  have hs : (0 : ℝ) < (scale : ℝ) := by norm_num [scale]
  rw [← mul_div_assoc,← sub_div]
  exact (le_div_iff₀ hs).mpr hr

theorem wide_newborn_deadline (γ : ℝ) (hγ : 0 ≤ γ)
    (hg : |γ-1/10| ≤ 1/10000000) (data : Nat → Array Int) (lim : Nat → Limits)
    (hcheck : ∀ m, 25 ≤ m → m < 50 → checkLayer m (data m) (data (m+1)) (lim m)=true)
    (hlim : ∀ m, 25 ≤ m → m < 50 → limitsOK m (lim m)=true)
    (hterminal : terminalCheck (data 50)=true) (hbirth : birthOK (data 25)=true)
    (col : Nat) (x : Fin 401) (y : Fin 101) (hb : wideNewborn col x.val y.val) :
    (991/1000 : ℝ) ≤ finiteTimeExpectation (wideFiniteModel γ hγ) 20
      (wideTerminalPayoff data col) (some ⟨0,x,y⟩) := by
  have hc := wide_newborn_count_bound col x.val y.val hb
  apply wide_checked_deadline γ hγ hg data lim hcheck hlim hterminal col hc.2.2.2
  · have hr := of_decide_eq_true (checked_row _ _ _ _
      (hcheck 25 (by norm_num) (by norm_num)) (x.val*101+y.val)
      (by norm_num [stateCount]; omega))
    have hv : (scale : ℝ) ≤ (value (data 25) (x.val*101+y.val) 2 : ℝ) := by
      exact_mod_cast hr.2.2.2.2.2.2.2.2
    norm_num [wideTimeWitness,wideValue]
    exact div_nonneg (le_trans (by norm_num [scale]) hv) (by norm_num [scale])
  · simpa [wideValue,wideTimeWitness] using checked_birth_fraction (data 25) hbirth col x.val y.val hb

end CompositionalMemory
