import proofs.CompositionalMemory.ReversibleFinitePayoff
import proofs.CompositionalMemory.ReversibleDeadlineBudget

namespace CompositionalMemory
open FiniteCopy FiniteIntegerRows ControlledRows
set_option maxRecDepth 2048

theorem reversible_newborn_budget (col : Fin 2) (x y : Nat)
    (hb : newborn 53 col.val x y) : x+y ≤ 874 := by
  unfold newborn at hb
  norm_num at hb
  omega

theorem reversible_initial_half_tail (data : Nat → Array Int)
    (hb : ReversibleRows.birthOK 53 (data 53)=true)
    (word : Fin 2 → Fin 2) (a : Fin 2 → Fin 849 × Fin 213)
    (ha : ∀ k, newborn 53 (word k).val (a k).1.val (a k).2.val) (k : Fin 2) :
    (19911/20000 : ℝ) ≤ coupledCurrent 53 data ⟨0,a⟩ k (word k).val-
      coupledCurrent 53 data ⟨0,a⟩ k 2/500000 := by
  let i := (a k).1.val*213+(a k).2.val
  have hi : i < stateCount 53 := by
    have hx := (a k).1.isLt
    have hy := (a k).2.isLt
    norm_num [stateCount,i]
    omega
  have hc := coupled_index_coordinates 53 (a k).1.val (a k).2.val
    (Nat.le_of_lt_succ (a k).2.isLt)
  have hix : i/213=(a k).1.val := hc.1
  have hiy : i%213=(a k).2.val := hc.2
  have hr := ReversibleRows.checked_birth_bound 53 (data 53) hb i hi (word k)
    (by simpa only [show 4*53+1=213 by norm_num,hix,hiy] using ha k)
  change (19911/20000 : ℝ) ≤ (value (data 53) i (word k).val : ℝ)/(precisionScale : ℝ)-
    ((value (data 53) i 2 : ℝ)/(precisionScale : ℝ))/500000
  rw [div_div,mul_comm (precisionScale : ℝ) (500000 : ℝ)]
  exact hr

/-- Uniform concrete-scale coupled deadline theorem. Its remaining premises
are decidable integer-table checks, never an assumed probability bound. -/
theorem reversible_uniform_deadline (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10)
    (data : Nat → Array Int)
    (hrows : ∀ m, 53 ≤ m → m < 106 → ReversibleRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ReversibleRows.terminalCheck 53 (data 106)=true)
    (hb : ReversibleRows.birthOK 53 (data 53)=true)
    (word : Fin 2 → Fin 2) (a : Fin 2 → Fin 849 × Fin 213)
    (ha : ∀ k, newborn 53 (word k).val (a k).1.val (a k).2.val) :
    (991/1000 : ℝ) ≤ finiteTimeExpectation (reversibleFiniteModel 53 ε hε) 20
      (coupledExactPayoff 53 word) (some ⟨0,a⟩) := by
  have hg := reversible_checked_generators 53 (by norm_num) ε hε hε1 data hrows ht word
  have hw : coupledJointTime 53 data (some ⟨0,a⟩)=
      (coupledCurrent 53 data ⟨0,a⟩ 0 2+coupledCurrent 53 data ⟨0,a⟩ 1 2)/2 := by
    norm_num [coupledJointTime,coupledCurrent]
    ring
  have hw0 := (reversible_current_bounds 53 data hrows ht ⟨0,a⟩ 0).2
  have hw1 := (reversible_current_bounds 53 data hrows ht ⟨0,a⟩ 1).2
  have hnonneg : 0 ≤ coupledJointTime 53 data (some ⟨0,a⟩) := by rw [hw]; linarith
  have hb0 := reversible_initial_half_tail data hb word a ha 0
  have hb1 := reversible_initial_half_tail data hb word a ha 1
  have hbirth : (495550 : ℝ) ≤ 500000*coupledJointValue 53 data word (some ⟨0,a⟩)-
      2*coupledJointTime 53 data (some ⟨0,a⟩) := by
    rw [hw]
    change (495550 : ℝ) ≤ 500000*(coupledCurrent 53 data ⟨0,a⟩ 0 (word 0).val+
      coupledCurrent 53 data ⟨0,a⟩ 1 (word 1).val-1)-_
    linarith only [hb0,hb1]
  exact reversible_deadline_from_generator (reversibleFiniteModel 53 ε hε)
    (coupledExactPayoff 53 word) (coupledJointValue 53 data word) (coupledJointTime 53 data)
    hg.1 hg.2 (reversible_value_cover 53 data hrows ht word) (some ⟨0,a⟩) hnonneg hbirth

end CompositionalMemory
