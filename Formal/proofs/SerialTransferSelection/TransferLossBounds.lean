import proofs.SerialTransferSelection.TransferLoss
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp

namespace SerialTransferSelection

noncomputable def transferLossProbability (n m c : ℕ) : ℝ :=
  ((n-c).choose m : ℝ)/(n.choose m : ℝ)

theorem transferLoss_product (n m c : ℕ) :
    transferLossProbability n m c =
      ∏ i ∈ Finset.range m, ((n-c-i : ℕ) : ℝ)/((n-i : ℕ) : ℝ) := by
  rw [Finset.prod_div_distrib,← Nat.cast_prod,← Nat.cast_prod,
    ← Nat.descFactorial_eq_prod_range,← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose,Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  unfold transferLossProbability
  rw [mul_div_mul_left _ _ hf]

theorem transferLoss_positive (n m c : ℕ) (hc : c ≤ n) (hm : m ≤ n-c) :
    0 < transferLossProbability n m c := by
  unfold transferLossProbability
  exact div_pos (by exact_mod_cast Nat.choose_pos hm)
    (by exact_mod_cast Nat.choose_pos (show m ≤ n by omega))

theorem transferLoss_impossible (n m c : ℕ) (h : n-c < m) :
    transferLossProbability n m c=0 := by
  simp [transferLossProbability,Nat.choose_eq_zero_of_lt h]

theorem transferLoss_factor (n c i : ℕ) (hi : i < n) (hci : c+i ≤ n) :
    ((n-c-i : ℕ) : ℝ)/((n-i : ℕ) : ℝ) = 1-(c : ℝ)/((n-i : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((n-i : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hi
  have he : ((n-c-i : ℕ) : ℝ) = ((n-i : ℕ) : ℝ)-(c : ℝ) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    ring
  rw [he]
  field_simp

/-- Standard exponential upper bound for conditional type loss. -/
theorem transferLoss_exp_upper (n m c : ℕ) (hc : c ≤ n) :
    transferLossProbability n m c ≤ Real.exp (-((m : ℝ)*c/n)) := by
  by_cases hm : m ≤ n-c
  · rw [transferLoss_product]
    have hb (i : ℕ) (hi : i ∈ Finset.range m) :
        ((n-c-i : ℕ) : ℝ)/((n-i : ℕ) : ℝ) ≤ Real.exp (-(c : ℝ)/n) := by
      have him : i < m := Finset.mem_range.mp hi
      rw [transferLoss_factor n c i (by omega) (by omega)]
      have hden : (0 : ℝ) < ((n-i : ℕ) : ℝ) := by exact_mod_cast (show 0 < n-i by omega)
      have hcmp := div_le_div₀ (Nat.cast_nonneg c : (0 : ℝ) ≤ c) le_rfl hden
        (show ((n-i : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.sub_le n i)
      have he := Real.add_one_le_exp (-(c : ℝ)/n)
      calc
        1-(c : ℝ)/((n-i : ℕ) : ℝ) ≤ 1-(c : ℝ)/n := sub_le_sub_left hcmp 1
        _ ≤ Real.exp (-(c : ℝ)/n) := by
          simpa only [neg_div,sub_eq_add_neg,add_comm] using he
    have hp := Finset.prod_le_prod (s := Finset.range m)
      (fun i _ => by positivity : ∀ i ∈ Finset.range m,
        (0 : ℝ) ≤ ((n-c-i : ℕ) : ℝ)/((n-i : ℕ) : ℝ)) hb
    simp only [Finset.prod_const,Finset.card_range] at hp
    apply hp.trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  · rw [transferLoss_impossible n m c (by omega)]
    exact (Real.exp_pos _).le

/-- A positive lower bound, obtained by sampling M times instead of exposing C
excluded cells. Its exponent convention differs from the guide's R2. -/
theorem transferLoss_lower (n m c : ℕ) (hc : c ≤ n) (hm : m ≤ n-c) :
    (1-(c : ℝ)/((n-m+1 : ℕ) : ℝ))^m ≤ transferLossProbability n m c := by
  rw [transferLoss_product]
  have hd : (0 : ℝ) < ((n-m+1 : ℕ) : ℝ) := by positivity
  have hbase : 0 ≤ 1-(c : ℝ)/((n-m+1 : ℕ) : ℝ) := by
    have hnum : (c : ℝ) ≤ ((n-m+1 : ℕ) : ℝ) := by exact_mod_cast (show c ≤ n-m+1 by omega)
    have hdiv := (div_le_one hd).mpr hnum
    linarith
  have hp := Finset.prod_le_prod (s := Finset.range m) (fun _ _ => hbase)
    (g := fun i => ((n-c-i : ℕ) : ℝ)/((n-i : ℕ) : ℝ)) (by
      intro i hi
      have him := Finset.mem_range.mp hi
      dsimp only
      rw [transferLoss_factor n c i (by omega) (by omega)]
      have hden : ((n-m+1 : ℕ) : ℝ) ≤ ((n-i : ℕ) : ℝ) := by
        exact_mod_cast (show n-m+1 ≤ n-i by omega)
      have hcmp := div_le_div₀ (Nat.cast_nonneg c : (0 : ℝ) ≤ c) le_rfl hd hden
      linarith)
  simpa only [Finset.prod_const,Finset.card_range] using hp

theorem transferLoss_lower_positive (n m c : ℕ) (hc : c ≤ n) (hm : m ≤ n-c) :
    0 < (1-(c : ℝ)/((n-m+1 : ℕ) : ℝ))^m := by
  apply pow_pos
  apply sub_pos.mpr
  apply (div_lt_one (by positivity : (0 : ℝ) < ((n-m+1 : ℕ) : ℝ))).mpr
  exact_mod_cast (show c < n-m+1 by omega)

end SerialTransferSelection
