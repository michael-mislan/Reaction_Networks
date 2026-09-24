import proofs.CompositionalMemory.WideGeneratorComparison
import proofs.CompositionalMemory.WideTerminalTransport

namespace CompositionalMemory
open FiniteCopy FiniteIntegerRows
set_option maxHeartbeats 60000

theorem wide_index_lt (j : Fin 26) (x : Fin (16*(25+j.val)+1))
    (y : Fin (4*(25+j.val)+1)) :
    x.val*(4*(25+j.val)+1)+y.val < stateCount (25+j.val) := by
  unfold stateCount
  have hh := Nat.mul_le_mul_right (4*(25+j.val)+1) (Nat.le_of_lt_succ x.isLt)
  nlinarith only [hh,y.isLt]

theorem wide_checked_generator (γ : ℝ) (hγ : 0 ≤ γ)
    (hg : |γ-1/10| ≤ 1/10000000) (data : Nat → Array Int) (lim : Nat → Limits)
    (hcheck : ∀ m, 25 ≤ m → m < 50 → checkLayer m (data m) (data (m+1)) (lim m)=true)
    (hlim : ∀ m, 25 ≤ m → m < 50 → limitsOK m (lim m)=true)
    (hterminal : terminalCheck (data 50)=true) :
    (∀ s, -(1/10000 : ℝ) ≤ (wideFiniteModel γ hγ).generator (wideValue data 0) s) ∧
    (∀ s, -(1/10000 : ℝ) ≤ (wideFiniteModel γ hγ).generator (wideValue data 1) s) ∧
    (∀ s, (wideFiniteModel γ hγ).generator (wideTimeWitness data) s ≤
      -(5/8 : ℝ)*wideTimeWitness data s+1/4000) := by
  have ht (x : Fin 801) (y : Fin 201) :
      0 ≤ (value (data 50) (x.val*201+y.val) 2 : ℝ) := by
    have hh := checked_terminal_rewards (data 50) hterminal (x.val*201+y.val)
      (by norm_num [stateCount]; nlinarith [x.isLt,y.isLt])
    have hs : (0 : ℝ) < (scale : ℝ) := by norm_num [scale]
    have he := (div_eq_one_iff_eq (ne_of_gt hs)).mp hh.2.2.2.2
    linarith
  have hlive (j : Fin 26) (hj : j.val≠25)
      (x : Fin (16*(25+j.val)+1)) (y : Fin (4*(25+j.val)+1)) :
      -(1/10000 : ℝ) ≤ (wideFiniteModel γ hγ).generator (wideValue data 0) (some ⟨j,x,y⟩) ∧
      -(1/10000 : ℝ) ≤ (wideFiniteModel γ hγ).generator (wideValue data 1) (some ⟨j,x,y⟩) ∧
      (wideFiniteModel γ hγ).generator (wideTimeWitness data) (some ⟨j,x,y⟩) ≤
        -(5/8 : ℝ)*wideTimeWitness data (some ⟨j,x,y⟩)+1/4000 := by
    have hm : 25+j.val < 50 := by omega
    have hm0 : 0 < 25+j.val := by omega
    have hr := checked_real_rows (25+j.val) hm0 _ _ _
      (hlim _ (by omega) hm) _
      (checked_row _ _ _ _ (hcheck _ (by omega) hm) _ (wide_index_lt j x y)) γ hg
    have hv0 := (abs_le.mp hr.1).1
    have hv1 := (abs_le.mp hr.2.1).1
    have hw := (abs_le.mp hr.2.2).2
    rw [← wideLiteral_integer_identity γ _ hm0] at hv0 hv1
    refine ⟨?_,?_,?_⟩
    · simpa [wide_generator_literal γ hγ data 0 j hj x y] using hv0
    · simpa [wide_generator_literal γ hγ data 1 j hj x y] using hv1
    · have hmono := wide_generator_mono_at γ hγ (wideTimeWitness data) (wideValue data 2)
        (some ⟨j,x,y⟩) (wideTimeWitness_le_value data ht) (by simp [wideTimeWitness,hj])
      rw [wide_generator_literal γ hγ data 2 j hj x y] at hmono
      have hexit := wideLiteral_outside_mono γ (25+j.val) (data (25+j.val))
        (data (25+j.val+1)) (x.val*(4*(25+j.val)+1)+y.val) 2 0 scale (by norm_num [scale])
      have hshift := wideLiteral_shifted_identity γ (25+j.val) hm0
        (data (25+j.val)) (data (25+j.val+1)) (x.val*(4*(25+j.val)+1)+y.val) 2
      rw [← wideLiteral_integer_identity γ _ hm0] at hshift
      simp only [ite_true] at hshift
      rw [mul_div_assoc] at hshift
      simp only [wideTimeWitness,hj,if_false,wideValue]
      linarith only [hmono,hexit,hshift,hw]
  have hall (s : WideFiniteState) :
      -(1/10000 : ℝ) ≤ (wideFiniteModel γ hγ).generator (wideValue data 0) s ∧
      -(1/10000 : ℝ) ≤ (wideFiniteModel γ hγ).generator (wideValue data 1) s ∧
      (wideFiniteModel γ hγ).generator (wideTimeWitness data) s ≤
        -(5/8 : ℝ)*wideTimeWitness data s+1/4000 := by
    cases s with
    | none => norm_num [wide_failure_absorbing,wideTimeWitness]
    | some s =>
      rcases s with ⟨j,x,y⟩
      by_cases hj : j.val=25
      · norm_num [wide_division_absorbing γ hγ _ j hj,wideTimeWitness,hj]
      · exact hlive j hj x y
  exact ⟨fun s => (hall s).1,fun s => (hall s).2.1,fun s => (hall s).2.2⟩

theorem wide_checked_cover (data : Nat → Array Int) (lim : Nat → Limits)
    (hcheck : ∀ m, 25 ≤ m → m < 50 → checkLayer m (data m) (data (m+1)) (lim m)=true)
    (col : Nat) (hc : col=0 ∨ col=1) :
    ∀ s, wideValue data col s ≤ wideTerminalPayoff data col s+wideTimeWitness data s := by
  intro s
  cases s with
  | none => simp [wideValue,wideTerminalPayoff,wideTimeWitness]
  | some s =>
    rcases s with ⟨j,x,y⟩
    by_cases hj : j.val=25
    · simp [wideTerminalPayoff,wideTimeWitness,hj]
    · have hr := of_decide_eq_true (checked_row _ _ _ _
        (hcheck (25+j.val) (by omega) (by omega)) _ (wide_index_lt j x y))
      have hh : value (data (25+j.val)) (x.val*(4*(25+j.val)+1)+y.val) col ≤
          value (data (25+j.val)) (x.val*(4*(25+j.val)+1)+y.val) 2 := by
        rcases hc with rfl | rfl
        · exact hr.2.2.2.2.2.2.1.trans hr.2.2.2.2.2.2.2.2
        · exact hr.2.2.2.2.2.2.2.1.trans hr.2.2.2.2.2.2.2.2
      simp only [wideTerminalPayoff,wideTimeWitness,hj,if_false,zero_add,wideValue]
      apply div_le_div_of_nonneg_right _ (by norm_num [scale])
      exact_mod_cast hh

/-- A conditional finite-source theorem: all finite row checks are explicit
hypotheses, and are not replaced by an asserted probability premise. -/
theorem wide_checked_deadline (γ : ℝ) (hγ : 0 ≤ γ)
    (hg : |γ-1/10| ≤ 1/10000000) (data : Nat → Array Int) (lim : Nat → Limits)
    (hcheck : ∀ m, 25 ≤ m → m < 50 → checkLayer m (data m) (data (m+1)) (lim m)=true)
    (hlim : ∀ m, 25 ≤ m → m < 50 → limitsOK m (lim m)=true)
    (hterminal : terminalCheck (data 50)=true)
    (col : Nat) (hc : col=0 ∨ col=1) (s : WideFiniteState)
    (hw : 0 ≤ wideTimeWitness data s)
    (hb : (248350 : ℝ) ≤ 250000*wideValue data col s-wideTimeWitness data s) :
    (991/1000 : ℝ) ≤ finiteTimeExpectation (wideFiniteModel γ hγ) 20
      (wideTerminalPayoff data col) s := by
  have hh := wide_checked_generator γ hγ hg data lim hcheck hlim hterminal
  apply wide_deadline_from_generator (wideFiniteModel γ hγ)
    (wideTerminalPayoff data col) (wideValue data col) (wideTimeWitness data)
    _ hh.2.2 (wide_checked_cover data lim hcheck col hc) s hw hb
  rcases hc with rfl | rfl
  · exact hh.1
  · exact hh.2.1

end CompositionalMemory
