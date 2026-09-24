import proofs.TypeIIL.LogarithmicSecantMatrix

namespace TypeIIL

/-- Continuous Bernoulli response, written in log coordinates. -/
noncomputable def bernoulliResponse (t : ℝ) : ℝ :=
  if t = 0 then 1 else t / (Real.exp t - 1)

@[simp] theorem bernoulliResponse_zero : bernoulliResponse 0 = 1 := by
  simp [bernoulliResponse]

theorem bernoulliResponse_pos (t : ℝ) : 0 < bernoulliResponse t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [bernoulliResponse, if_neg (ne_of_lt ht)]
    exact div_pos_of_neg_of_neg ht (sub_neg.mpr (by
      simpa using (Real.exp_lt_exp.mpr ht)))
  · simp
  · rw [bernoulliResponse, if_neg (ne_of_gt ht)]
    exact div_pos ht (sub_pos.mpr (by
      simpa using (Real.exp_lt_exp.mpr ht)))

theorem bernoulliResponse_neg (t : ℝ) :
    bernoulliResponse (-t) = t + bernoulliResponse t := by
  by_cases ht : t = 0
  · simp [ht]
  · have hnt : -t ≠ 0 := neg_ne_zero.mpr ht
    have he : Real.exp t - 1 ≠ 0 := by
      intro h
      have : Real.exp t = 1 := by linarith
      have hlog := congrArg Real.log this
      exact ht (by simpa using hlog)
    have he' : 1 - Real.exp t ≠ 0 := by
      intro h
      exact he (by linarith)
    unfold bernoulliResponse
    simp only [if_neg ht, if_neg hnt]
    rw [Real.exp_neg]
    field_simp [he, he', Real.exp_ne_zero]
    ring

theorem bernoulliResponse_le_one {t : ℝ} (ht : 0 ≤ t) :
    bernoulliResponse t ≤ 1 := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  · rw [bernoulliResponse, if_neg (ne_of_gt ht)]
    have hden : 0 < Real.exp t - 1 := sub_pos.mpr (by
      simpa using (Real.exp_lt_exp.mpr ht))
    exact (div_le_one hden).2 (by
      linarith [Real.add_one_le_exp t])

theorem one_le_bernoulliResponse_neg {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ bernoulliResponse (-t) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  · have hden : 0 < Real.exp t - 1 := sub_pos.mpr (by
      simpa using (Real.exp_lt_exp.mpr ht))
    have he : Real.exp t ≠ 0 := Real.exp_ne_zero t
    have he' : 1 - Real.exp t ≠ 0 := by linarith
    have hform : (-t) / (Real.exp (-t) - 1) =
        t * Real.exp t / (Real.exp t - 1) := by
      rw [Real.exp_neg]
      field_simp [he, he']
      ring
    rw [bernoulliResponse, if_neg (neg_ne_zero.mpr (ne_of_gt ht)), hform]
    apply (le_div_iff₀ hden).2
    have hlog := Real.self_sub_one_le_mul_log (le_of_lt (Real.exp_pos t))
    simpa [mul_comm] using hlog

theorem one_sub_le_bernoulliResponse {t : ℝ} (ht : 0 ≤ t) :
    1 - t ≤ bernoulliResponse t := by
  have hneg := one_le_bernoulliResponse_neg ht
  rw [bernoulliResponse_neg] at hneg
  linarith

theorem bernoulliResponse_add_pos_strict {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    bernoulliResponse (x + y) <
      bernoulliResponse x + bernoulliResponse y := by
  have hxy : 0 < x + y := add_pos hx hy
  have hdx : 0 < Real.exp x - 1 := sub_pos.mpr (by
    simpa using (Real.exp_lt_exp.mpr hx))
  have hdy : 0 < Real.exp y - 1 := sub_pos.mpr (by
    simpa using (Real.exp_lt_exp.mpr hy))
  have hdxy : 0 < Real.exp (x + y) - 1 := sub_pos.mpr (by
    simpa using (Real.exp_lt_exp.mpr hxy))
  have hdxxy : Real.exp x - 1 < Real.exp (x + y) - 1 := by
    have := Real.exp_lt_exp.mpr (lt_add_of_pos_right x hy)
    linarith
  have hdyxy : Real.exp y - 1 < Real.exp (x + y) - 1 := by
    have := Real.exp_lt_exp.mpr (lt_add_of_pos_left y hx)
    linarith
  rw [bernoulliResponse, if_neg (ne_of_gt hxy),
    bernoulliResponse, if_neg (ne_of_gt hx),
    bernoulliResponse, if_neg (ne_of_gt hy), add_div]
  have hxpart : x / (Real.exp (x + y) - 1) < x / (Real.exp x - 1) :=
    div_lt_div_of_pos_left hx hdx hdxxy
  have hypart : y / (Real.exp (x + y) - 1) < y / (Real.exp y - 1) :=
    div_lt_div_of_pos_left hy hdy hdyxy
  linarith

theorem bernoulliResponse_add_nonneg_strict {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    bernoulliResponse (x + y) <
      bernoulliResponse x + bernoulliResponse y := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · rw [zero_add, bernoulliResponse_zero]
    linarith [bernoulliResponse_pos y]
  rcases eq_or_lt_of_le hy with rfl | hy
  · rw [add_zero, bernoulliResponse_zero]
    linarith [bernoulliResponse_pos x]
  exact bernoulliResponse_add_pos_strict hx hy

theorem bernoulliResponse_add_of_nonneg_of_neg {x y : ℝ}
    (hx : 0 ≤ x) (hy : y < 0) :
    bernoulliResponse (x + y) <
      bernoulliResponse x + bernoulliResponse y := by
  let b := -y
  have hb : 0 < b := neg_pos.mpr hy
  rw [show y = -b by simp [b], bernoulliResponse_neg]
  by_cases hxb : b ≤ x
  · have hz : 0 ≤ x - b := sub_nonneg.mpr hxb
    have htarget := bernoulliResponse_le_one hz
    have hbase := one_sub_le_bernoulliResponse (le_of_lt hb)
    have hpos := bernoulliResponse_pos x
    change bernoulliResponse (x - b) <
      bernoulliResponse x + (b + bernoulliResponse b)
    linarith
  · have hbx : x < b := lt_of_not_ge hxb
    let c := b - x
    have hc : 0 < c := sub_pos.mpr hbx
    change bernoulliResponse (x - b) <
      bernoulliResponse x + (b + bernoulliResponse b)
    rw [show x - b = -c by simp [c], bernoulliResponse_neg]
    have htarget := bernoulliResponse_le_one (le_of_lt hc)
    have hbase := one_sub_le_bernoulliResponse hx
    have hpos := bernoulliResponse_pos b
    dsimp [c]
    linarith

/-- The Bernoulli response is strictly subadditive on all of `ℝ`. -/
theorem bernoulliResponse_add_strict (x y : ℝ) :
    bernoulliResponse (x + y) <
      bernoulliResponse x + bernoulliResponse y := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · exact bernoulliResponse_add_nonneg_strict hx hy
    · exact bernoulliResponse_add_of_nonneg_of_neg hx (lt_of_not_ge hy)
  · have hx' : x < 0 := lt_of_not_ge hx
    by_cases hy : 0 ≤ y
    · simpa [add_comm] using
        (bernoulliResponse_add_of_nonneg_of_neg hy hx')
    · have hy' : y < 0 := lt_of_not_ge hy
      let a := -x
      let b := -y
      have ha : 0 < a := neg_pos.mpr hx'
      have hb : 0 < b := neg_pos.mpr hy'
      have hxa : bernoulliResponse x = a + bernoulliResponse a := by
        rw [show x = -a by simp [a], bernoulliResponse_neg]
      have hyb : bernoulliResponse y = b + bernoulliResponse b := by
        rw [show y = -b by simp [b], bernoulliResponse_neg]
      have hsum : bernoulliResponse (x + y) =
          a + b + bernoulliResponse (a + b) := by
        calc
          bernoulliResponse (x + y) = bernoulliResponse (-(a + b)) := by
            congr 1
            dsimp [a, b]
            ring
          _ = a + b + bernoulliResponse (a + b) := by
            rw [bernoulliResponse_neg]
      have hpos := bernoulliResponse_add_nonneg_strict
        (le_of_lt ha) (le_of_lt hb)
      rw [hsum, hxa, hyb]
      linarith

/-- In logarithmic coordinates the Bernoulli response is exactly the
reciprocal logarithmic secant. -/
theorem inv_logSecant_exp_eq_bernoulliResponse (t : ℝ) :
    1 / logSecant (Real.exp t) = bernoulliResponse t := by
  by_cases ht : t = 0
  · simp [ht, logSecant, bernoulliResponse]
  · have hexp : Real.exp t ≠ 1 := by
      intro h
      have hlog := congrArg Real.log h
      exact ht (by simpa using hlog)
    simp [logSecant, bernoulliResponse, ht, hexp, Real.log_exp]

/-- Finite nonempty sums inherit Bernoulli subadditivity. -/
theorem bernoulliResponse_list_sum_le (xs : List ℝ) (hxs : xs ≠ []) :
    bernoulliResponse xs.sum ≤ (xs.map bernoulliResponse).sum := by
  induction xs with
  | nil => exact (hxs rfl).elim
  | cons x xs ih =>
      by_cases htail : xs = []
      · simp [htail]
      · have hadd := bernoulliResponse_add_strict x xs.sum
        have hrest := ih htail
        simp only [List.sum_cons, List.map_cons]
        linarith

/-- A list containing at least two exponent copies gives a strict row-sum
gain. -/
theorem bernoulliResponse_list_sum_strict (x y : ℝ) (xs : List ℝ) :
    bernoulliResponse (x :: y :: xs).sum <
      ((x :: y :: xs).map bernoulliResponse).sum := by
  have hadd := bernoulliResponse_add_strict x (y :: xs).sum
  have hrest := bernoulliResponse_list_sum_le (y :: xs) (by simp)
  simp only [List.sum_cons, List.map_cons] at hadd hrest ⊢
  linarith

/-- Exact strict logarithmic-secant row gain for a monomial represented as a
list of at least two log-ratio factor copies. -/
theorem logSecant_exp_list_row_sum_strict (x y : ℝ) (xs : List ℝ) :
    1 < logSecant (Real.exp (x :: y :: xs).sum) *
      (((x :: y :: xs).map
        (fun t => 1 / logSecant (Real.exp t))).sum) := by
  have h := bernoulliResponse_list_sum_strict x y xs
  simp_rw [← inv_logSecant_exp_eq_bernoulliResponse] at h
  have hL : 0 < logSecant (Real.exp (x :: y :: xs).sum) :=
    logSecant_pos (Real.exp_pos _)
  have hmul := (div_lt_iff₀ hL).mp h
  simpa only [inv_logSecant_exp_eq_bernoulliResponse, mul_comm] using hmul

theorem bernoulliResponse_nat_mul_le (x : ℝ) {m : ℕ} (hm : 0 < m) :
    bernoulliResponse ((m : ℝ) * x) ≤
      (m : ℝ) * bernoulliResponse x := by
  induction m with
  | zero => simp at hm
  | succ m ih =>
      by_cases hm0 : m = 0
      · simp [hm0]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        have hadd := bernoulliResponse_add_strict ((m : ℝ) * x) x
        have hprev := ih hmpos
        apply le_of_lt
        calc
          bernoulliResponse (((m + 1 : ℕ) : ℝ) * x) =
              bernoulliResponse ((m : ℝ) * x + x) := by
                congr 1
                push_cast
                ring
          _ < bernoulliResponse ((m : ℝ) * x) + bernoulliResponse x := hadd
          _ ≤ (m : ℝ) * bernoulliResponse x + bernoulliResponse x :=
            add_le_add hprev le_rfl
          _ = ((m + 1 : ℕ) : ℝ) * bernoulliResponse x := by
            push_cast
            ring

/-- Strict row gain for one factor together with a positive number of repeated
copies of another factor, the exact Type II_l fork monomial shape. -/
theorem logSecant_exp_weighted_fork_row_sum_strict
    (x y : ℝ) {m : ℕ} (hm : 0 < m) :
    1 < logSecant (Real.exp ((m : ℝ) * x + y)) *
      ((m : ℝ) / logSecant (Real.exp x) +
        1 / logSecant (Real.exp y)) := by
  have hadd := bernoulliResponse_add_strict ((m : ℝ) * x) y
  have hmul := bernoulliResponse_nat_mul_le x hm
  have hstrict : bernoulliResponse ((m : ℝ) * x + y) <
      (m : ℝ) * bernoulliResponse x + bernoulliResponse y := by
    linarith
  simp_rw [← inv_logSecant_exp_eq_bernoulliResponse] at hstrict
  have hL : 0 < logSecant (Real.exp ((m : ℝ) * x + y)) :=
    logSecant_pos (Real.exp_pos _)
  have hscaled := (div_lt_iff₀ hL).mp hstrict
  simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc]
    using hscaled

/-- Concentration-ratio form of the strict Type II_l fork row gain. -/
theorem weighted_fork_logSecant_row_sum_strict
    {P R : ℝ} (hP : 0 < P) (hR : 0 < R) {m : ℕ} (hm : 0 < m) :
    1 < logSecant (P * R ^ m) *
      ((m : ℝ) / logSecant R + 1 / logSecant P) := by
  have h := logSecant_exp_weighted_fork_row_sum_strict
    (Real.log R) (Real.log P) hm
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hR,
    Real.exp_log hP] at h
  simpa [mul_comm] using h

/-- Matrix-row docking for a weighted Type II_l fork product.  The two
displayed identities are the literal sparse-column computations: the product
monomial is `Pback * R^m`, and the exponent row has entries `m` and `1`. -/
theorem logarithmicSecantMatrix_fork_row_sum_strict
    {ι : Type*} [Fintype ι]
    (P : ι → ι → ℕ) {rho : ι → ℝ} (r : ι)
    {Pback R : ℝ} {m : ℕ}
    (hPback : 0 < Pback) (hR : 0 < R) (hm : 0 < m)
    (hmonomial : monomialRatio P rho r = Pback * R ^ m)
    (hexponents :
      ∑ i, (P i r : ℝ) / logSecant (rho i) =
        (m : ℝ) / logSecant R + 1 / logSecant Pback) :
    1 < ∑ i, logarithmicSecantMatrix P rho r i := by
  unfold logarithmicSecantMatrix
  rw [show (∑ i, logSecant (monomialRatio P rho r) * (P i r : ℝ) /
        logSecant (rho i)) =
      logSecant (monomialRatio P rho r) *
        ∑ i, (P i r : ℝ) / logSecant (rho i) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [hmonomial, hexponents]
  exact weighted_fork_logSecant_row_sum_strict hPback hR hm

end TypeIIL
