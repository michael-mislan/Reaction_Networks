import proofs.RAFReactionCriticality.FiniteThinning

namespace RAFReactionCriticality.FiniteProductDerivative
open FiniteThinning
open scoped BigOperators
variable {R : Type*} [Fintype R] [DecidableEq R]

def join (i : R) (b : Bool) (m : {j : R // j ≠ i} → Bool) : R → Bool :=
  (Equiv.funSplitAt i Bool).symm (b, m)

omit [Fintype R] in
@[simp] theorem join_same (i : R) (b : Bool) (m : {j : R // j ≠ i} → Bool) :
    join i b m i = b := by simp [join, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype R] in
@[simp] theorem join_other (i : R) (b : Bool) (m : {j : R // j ≠ i} → Bool)
    (j : R) (h : j ≠ i) : join i b m j = m ⟨j,h⟩ := by
  simp [join, Equiv.funSplitAt, Equiv.piSplitAt, h]

theorem sum_split (i : R) (F : (R → Bool) → ℝ) :
    (∑ m, F m) = ∑ m : {j : R // j ≠ i} → Bool,
      (F (join i false m) + F (join i true m)) := by
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, join, Finset.sum_add_distrib]
  ring

def offWeight (p : ℝ) (i : R) (m : R → Bool) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, if m j then p else 1-p

theorem offWeight_join (p : ℝ) (i : R) (m : {j : R // j ≠ i} → Bool) :
    offWeight p i (join i true m) = offWeight p i (join i false m) := by
  apply Finset.prod_congr rfl
  intro j hj
  have h := (Finset.mem_erase.mp hj).1
  simp [join_other, h]

noncomputable def expectation (F : (R → Bool) → ℝ) (p : ℝ) : ℝ :=
  ∑ m, weight p m * F m

noncomputable def marginal (F : (R → Bool) → ℝ) (p : ℝ) (i : R) : ℝ :=
  ∑ m : {j : R // j ≠ i} → Bool,
    offWeight p i (join i false m) * (F (join i true m) - F (join i false m))

theorem coordinate_sum (F : (R → Bool) → ℝ) (p : ℝ) (i : R) :
    (∑ m : R → Bool, (if m i then (1 : ℝ) else -1) * offWeight p i m * F m) =
      marginal F p i := by
  rw [sum_split i]
  apply Finset.sum_congr rfl
  intro m _
  simp only [join_same, Bool.false_eq_true, ↓reduceIte, offWeight_join]
  ring

theorem weight_derivative (m : R → Bool) (p : ℝ) :
    HasDerivAt (fun q => weight q m)
      (∑ i, (if m i then (1 : ℝ) else -1) * offWeight p i m) p := by
  have hi (i : R) : HasDerivAt (fun q : ℝ => if m i then q else 1-q)
      (if m i then (1 : ℝ) else -1) p := by
    cases hm : m i
    · simpa only [hm, Bool.false_eq_true, ↓reduceIte, zero_sub] using
        (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
    · simpa only [hm, ↓reduceIte] using hasDerivAt_id p
  simpa only [weight, offWeight, smul_eq_mul, mul_comm] using
    HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hi i)

/-- Finite real-valued Russo identity under the exact independent-mask law. -/
theorem expectation_derivative (F : (R → Bool) → ℝ) (p : ℝ) :
    HasDerivAt (expectation F) (∑ i, marginal F p i) p := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun m _ => (weight_derivative m p).mul_const (F m))
  have he : (∑ m : R → Bool,
      (∑ i, (if m i then (1 : ℝ) else -1) * offWeight p i m) * F m) =
      ∑ i, marginal F p i := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => coordinate_sum F p i)
  simpa only [he] using hd

theorem offWeight_one (i : R) (m : {j : R // j ≠ i} → Bool) :
    offWeight 1 i (join i false m) = if m = (fun _ => true) then 1 else 0 := by
  classical
  by_cases h : m = (fun _ => true)
  · subst m
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  · rw [if_neg h]
    have hex : ∃ j, m j ≠ true := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    obtain ⟨j,hj⟩ := hex
    have hf : m j = false := Bool.eq_false_iff.mpr hj
    apply Finset.prod_eq_zero (i := j.val)
    · simp [j.property]
    · simp [join_other, j.property, hf]

theorem marginal_one (F : (R → Bool) → ℝ) (i : R) :
    marginal F 1 i = F (fun _ => true) - F (Function.update (fun _ => true) i false) := by
  classical
  have ht : join i true (fun _ => true) = (fun _ => true) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  have hf : join i false (fun _ => true) = Function.update (fun _ => true) i false := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj, Function.update_of_ne]
  simp only [marginal, offWeight_one, ite_mul, one_mul, zero_mul]
  simp [ht, hf]

theorem expectation_derivative_one (F : (R → Bool) → ℝ) :
    HasDerivAt (expectation F)
      (∑ i, (F (fun _ => true) - F (Function.update (fun _ => true) i false))) 1 := by
  simpa only [marginal_one] using expectation_derivative F 1

end RAFReactionCriticality.FiniteProductDerivative
