import proofs.FiniteCopyReactor.Margins
import proofs.RandomViability.BindingEntryExponential

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

/-- Categories: retained, withdrawn, additional loss. -/
def categoryMass (p : Intervention) (i : Fin 6) : Fin 3 → ℝ :=
  ![p.q*p.loss i, 1-p.q, p.q*(1-p.loss i)]

theorem category_nonneg (p : Intervention) (i : Fin 6) (a : Fin 3) :
    0 ≤ categoryMass p i a := by
  have hq : 0 ≤ p.q := by linarith [p.q_lower]
  have hl : 0 ≤ p.loss i := by linarith [p.loss_lower i]
  fin_cases a <;> norm_num [categoryMass]
  · positivity
  · linarith [p.q_upper]
  · exact mul_nonneg hq (sub_nonneg.mpr (p.loss_upper i))

theorem category_total (p : Intervention) (i : Fin 6) :
    ∑ a, categoryMass p i a = 1 := by
  norm_num [categoryMass, Fin.sum_univ_succ]
  ring

abbrev Molecules (N : Counts) := (i : Fin 6) × Fin (N i)
abbrev PulseOutcome (N : Counts) := Molecules N → Fin 3

/-- Exact finite product law on molecule categories; retains all failure mass. -/
def pulseMass (N : Counts) (p : Intervention) (o : PulseOutcome N) : ℝ :=
  ∏ m, categoryMass p m.1 (o m)

theorem pulseMass_nonneg (N : Counts) (p : Intervention) (o : PulseOutcome N) :
    0 ≤ pulseMass N p o := Finset.prod_nonneg (fun m _ => category_nonneg p m.1 (o m))

theorem pulseMass_total (N : Counts) (p : Intervention) :
    ∑ o, pulseMass N p o = 1 := by
  classical
  unfold pulseMass
  rw [← Fintype.prod_sum]
  simp only [category_total, Finset.prod_const_one]

def retainedStock (N : Counts) (w : Molecules N → ℝ) (o : PulseOutcome N) : ℝ :=
  ∑ m, if o m = 0 then w m else 0

theorem pulse_laplace (N : Counts) (p : Intervention) (w : Molecules N → ℝ) (s : ℝ) :
    (∑ o, pulseMass N p o * Real.exp (-s*retainedStock N w o)) =
      ∏ m, (1-p.q*p.loss m.1+p.q*p.loss m.1*Real.exp (-s*w m)) := by
  classical
  have hid (o : PulseOutcome N) :
      pulseMass N p o * Real.exp (-s*retainedStock N w o) =
        ∏ m, categoryMass p m.1 (o m) * Real.exp (-s*(if o m=0 then w m else 0)) := by
    unfold pulseMass retainedStock
    rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
  simp_rw [hid]
  rw [← Fintype.prod_sum (fun (m : Molecules N) (a : Fin 3) =>
    categoryMass p m.1 a * Real.exp (-s*(if a=0 then w m else 0)))]
  apply Finset.prod_congr rfl
  intro m _
  norm_num [categoryMass, Fin.sum_univ_succ]
  ring

/-- Source-independent one-molecule factor; the sum of factors is the actual mean. -/
theorem retention_factor_bound (p w s : ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hw' : w ≤ 9/5) (hs : 0 ≤ s) (hs' : s ≤ 1/10) :
    1-p+p*Real.exp (-s*w) ≤ Real.exp (-(s-(27/25)*s^2)*(p*w)) := by
  have hab : |-s*w| ≤ 9/50 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hs, abs_of_nonneg hw]
    exact (mul_le_mul hs' hw' hw (by norm_num)).trans (by norm_num)
  have he := mul_le_mul_of_nonneg_left (exp_small_quadratic (-s*w) hab) hp
  have hw2 : w^2 ≤ (9/5)*w := by nlinarith
  have hq := mul_le_mul_of_nonneg_left hw2 (show 0 ≤ (3/5)*p*s^2 by positivity)
  have hlin : 1-p+p*Real.exp (-s*w) ≤ 1+(-(s-(27/25)*s^2)*(p*w)) := by
    nlinarith
  exact hlin.trans (by simpa only [add_comm] using Real.add_one_le_exp (-(s-(27/25)*s^2)*(p*w)))

theorem retention_probability_bounds (p : Intervention) (i : Fin 6) :
    49/200 ≤ p.q*p.loss i ∧ p.q*p.loss i ≤ 1 := by
  have hq : 0 ≤ p.q := by linarith [p.q_lower]
  have hl : 0 ≤ p.loss i := by linarith [p.loss_lower i]
  constructor
  · have h := mul_le_mul p.q_lower (p.loss_lower i) (by norm_num : (0:ℝ) ≤ 49/50) hq
    norm_num at h
    exact h
  · have h := mul_le_mul p.q_upper (p.loss_upper i) hl (by norm_num : (0:ℝ) ≤ 3/4)
    nlinarith

theorem pulse_laplace_bound (N : Counts) (p : Intervention) (w : Molecules N → ℝ)
    (hw : ∀ m, 0 ≤ w m) (hw' : ∀ m, w m ≤ 9/5)
    (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1/10) :
    (∑ o, pulseMass N p o * Real.exp (-s*retainedStock N w o)) ≤
      Real.exp (-(s-(27/25)*s^2)*(∑ m, p.q*p.loss m.1*w m)) := by
  classical
  rw [pulse_laplace, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro m _
    obtain ⟨hl,hu⟩ := retention_probability_bounds p m.1
    have hp : 0 ≤ p.q*p.loss m.1 := by linarith
    exact add_nonneg (sub_nonneg.mpr hu) (mul_nonneg hp (Real.exp_pos _).le)
  · intro m _
    apply retention_factor_bound _ _ s _ (hw m) (hw' m) hs hs'
    linarith [(retention_probability_bounds p m.1).1]

def pulseTail (N : Counts) (p : Intervention) (w : Molecules N → ℝ) (a : ℝ) : ℝ :=
  ∑ o, if retainedStock N w o ≤ a then pulseMass N p o else 0

theorem pulse_chernoff (N : Counts) (p : Intervention) (w : Molecules N → ℝ)
    (hw : ∀ m, 0 ≤ w m) (hw' : ∀ m, w m ≤ 9/5)
    (s a : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1/10) :
    pulseTail N p w a ≤
      Real.exp (s*a-(s-(27/25)*s^2)*(∑ m, p.q*p.loss m.1*w m)) := by
  classical
  have ht : Real.exp (-s*a)*pulseTail N p w a ≤
      ∑ o, pulseMass N p o * Real.exp (-s*retainedStock N w o) := by
    unfold pulseTail
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro o _
    split_ifs with ho
    · have he : Real.exp (-s*a) ≤ Real.exp (-s*retainedStock N w o) :=
        Real.exp_le_exp.mpr (by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_left he (pulseMass_nonneg N p o)]
    · simp only [mul_zero]
      exact mul_nonneg (pulseMass_nonneg N p o) (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left
    (ht.trans (pulse_laplace_bound N p w hw hw' s hs hs')) (Real.exp_pos (s*a)).le
  have hcancel : Real.exp (s*a)*Real.exp (-s*a) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [← mul_assoc, hcancel, one_mul, ← Real.exp_add] at h
  convert h using 1
  congr 1
  ring

/-- Uniform low-retention tail for the literal molecule category law. -/
theorem pulse_stock_tail (N : Counts) (p : Intervention) (w : Molecules N → ℝ)
    (V : ℝ) (hw : ∀ m, 0 ≤ w m) (hw' : ∀ m, w m ≤ 9/5)
    (hstock : V/20 ≤ ∑ m, w m) :
    pulseTail N p w ((3/250)*V) ≤ Real.exp (-(1177/1000000000)*V) := by
  have hm : (49/200)*(∑ m, w m) ≤ ∑ m, p.q*p.loss m.1*w m := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun m _ =>
      mul_le_mul_of_nonneg_right (retention_probability_bounds p m.1).1 (hw m))
  have h := pulse_chernoff N p w hw hw' (1/100) ((3/250)*V) (by norm_num) (by norm_num)
  apply h.trans
  apply Real.exp_le_exp.mpr
  linarith

end
end FiniteCopyReactor
