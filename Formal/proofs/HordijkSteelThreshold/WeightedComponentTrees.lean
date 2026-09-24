import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace HordijkSteelThreshold

/-- A finite-depth tree majorant. Its use for connected sets requires a separate
combinatorial covering theorem; this definition does not assume that theorem. -/
noncomputable def componentTreeMajorant {V : Type*} (neighbors : V → Finset V)
    (weight : V → ℝ) : ℕ → V → ℝ
  | 0, x => weight x
  | k + 1, x => weight x * ∏ y ∈ neighbors x,
      (1 + componentTreeMajorant neighbors weight k y)

theorem componentTreeMajorant_nonneg {V : Type*} (neighbors : V → Finset V)
    (weight : V → ℝ) (hw : ∀ x, 0 ≤ weight x) (k : ℕ) (x : V) :
    0 ≤ componentTreeMajorant neighbors weight k x := by
  induction k generalizing x with
  | zero => exact hw x
  | succ k ih =>
    exact mul_nonneg (hw x)
      (Finset.prod_nonneg fun y _ => add_nonneg zero_le_one (ih y))

/-- A uniform supersolution controls every finite tree depth. -/
theorem componentTreeMajorant_le_supersolution {V : Type*}
    (neighbors : V → Finset V) (weight : V → ℝ) (b : ℝ)
    (hw : ∀ x, 0 ≤ weight x) (hb : 0 ≤ b)
    (hs : ∀ x, weight x * Real.exp ((neighbors x).card * b) ≤ b)
    (k : ℕ) (x : V) : componentTreeMajorant neighbors weight k x ≤ b := by
  induction k generalizing x with
  | zero =>
    have he : 1 ≤ Real.exp ((neighbors x).card * b) :=
      Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hb)
    exact (le_mul_of_one_le_right (hw x) he).trans (hs x)
  | succ k ih =>
    have hp := Real.prod_one_add_le_exp_sum (neighbors x)
      (componentTreeMajorant_nonneg neighbors weight hw k)
    have hsum : (∑ y ∈ neighbors x, componentTreeMajorant neighbors weight k y)
        ≤ (neighbors x).card * b := by
      calc
        _ ≤ ∑ _y ∈ neighbors x, b := Finset.sum_le_sum fun y _ => ih y
        _ = _ := by simp
    exact (mul_le_mul_of_nonneg_left
      (hp.trans (Real.exp_le_exp.mpr hsum)) (hw x)).trans (hs x)

/-- Degree-dependent exponential weights absorb neighbor branching uniformly in
depth. Reaction degree may exceed distinct-neighbor degree (parallel edges). -/
theorem componentTreeMajorant_exp_bound {V : Type*}
    (neighbors : V → Finset V) (degree : V → ℕ) (c w : ℝ)
    (hc : 0 ≤ c)
    (hcard : ∀ x, (neighbors x).card ≤ degree x)
    (hdegree : ∀ x, 2 * w ≤ (degree x : ℝ))
    (heta : Real.exp (1 - c * w) ≤ c / 2)
    (k : ℕ) (x : V) :
    componentTreeMajorant neighbors (fun y => Real.exp (1 - c * degree y)) k x
      ≤ Real.exp (1 - (c / 2) * degree x) := by
  have hb : 0 ≤ c / 2 := by positivity
  have hs : ∀ y, Real.exp (1 - c * degree y) *
      Real.exp ((neighbors y).card * (c / 2)) ≤ c / 2 := by
    intro y
    rw [← Real.exp_add]
    apply le_trans _ heta
    apply Real.exp_le_exp.mpr
    have hd := hdegree y
    have hn : ((neighbors y).card : ℝ) ≤ degree y := by exact_mod_cast hcard y
    nlinarith
  cases k with
  | zero =>
    apply Real.exp_le_exp.mpr
    have hd : 0 ≤ (degree x : ℝ) := Nat.cast_nonneg _
    nlinarith
  | succ k =>
    have hi := componentTreeMajorant_le_supersolution neighbors
      (fun y => Real.exp (1 - c * degree y)) (c / 2)
      (fun y => (Real.exp_pos _).le) hb hs k
    have hp := Real.prod_one_add_le_exp_sum (neighbors x)
      (componentTreeMajorant_nonneg neighbors
        (fun y => Real.exp (1 - c * degree y))
        (fun y => (Real.exp_pos _).le) k)
    have hsum : (∑ y ∈ neighbors x,
        componentTreeMajorant neighbors (fun y => Real.exp (1 - c * degree y)) k y)
        ≤ (neighbors x).card * (c / 2) := by
      calc
        _ ≤ ∑ _y ∈ neighbors x, c / 2 := Finset.sum_le_sum fun y _ => hi y
        _ = _ := by simp
    calc
      _ ≤ Real.exp (1 - c * degree x) *
          Real.exp ((neighbors x).card * (c / 2)) :=
        mul_le_mul_of_nonneg_left (hp.trans (Real.exp_le_exp.mpr hsum))
          (Real.exp_pos _).le
      _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hn : ((neighbors x).card : ℝ) ≤ degree x := by exact_mod_cast hcard x
        nlinarith

end HordijkSteelThreshold
