import proofs.FiniteCopy.FiniteKernel

namespace RandomViability.Binding
noncomputable section
open FiniteCopy

theorem capped_mul_identity (cap a x : ℝ) (hc : 0 ≤ cap) (ha : 1 ≤ a) :
    min cap (a*min cap x) = min cap (a*x) := by
  by_cases hx : x ≤ cap
  · rw [min_eq_right hx]
  · have hx' : cap ≤ x := le_of_not_ge hx
    have hc' : cap ≤ a*cap := by nlinarith
    have hax : cap ≤ a*x := hc'.trans (mul_le_mul_of_nonneg_left hx' (by linarith))
    rw [min_eq_left hx',min_eq_left hc',min_eq_left hax]

theorem steps_capped_growth {α : Type*} [Fintype α] (P : FiniteKernel α)
    (F : ℝ → α → ℝ) (cap a s : ℝ) (hc : 0 ≤ cap) (ha : 1 ≤ a)
    (hs : 0 ≤ s) (hsc : s ≤ cap)
    (hstep : ∀ t, 0 ≤ t → t ≤ cap → ∀ x,
      P.step (F t) x ≤ F (min cap (a*t)) x) (n : ℕ) (x : α) :
    P.steps n (F s) x ≤ F (min cap (s*a^n)) x := by
  induction n generalizing x with
  | zero => simp [FiniteKernel.steps,min_eq_right hsc]
  | succ n ih =>
    have hm := P.step_mono ih x
    have hn : 0 ≤ s*a^n := mul_nonneg hs (pow_nonneg (by linarith) _)
    have hh := hstep (min cap (s*a^n)) (le_min hc hn) (min_le_left _ _) x
    rw [capped_mul_identity cap a (s*a^n) hc ha] at hh
    have he : a*(s*a^n) = s*a^(n+1) := by rw [pow_succ]; ring
    rw [he] at hh
    exact hm.trans hh

theorem steps_capped_target {α : Type*} [Fintype α] (P : FiniteKernel α)
    (F : ℝ → α → ℝ) (cap a s target : ℝ) (hc : 0 ≤ cap) (ha : 1 ≤ a)
    (hs : 0 ≤ s) (hsc : s ≤ cap)
    (hanti : ∀ u v, u ≤ v → ∀ x, F v x ≤ F u x)
    (hstep : ∀ t, 0 ≤ t → t ≤ cap → ∀ x,
      P.step (F t) x ≤ F (min cap (a*t)) x)
    (n : ℕ) (htc : target ≤ cap) (ht : target ≤ s*a^n) (x : α) :
    P.steps n (F s) x ≤ F target x :=
  (steps_capped_growth P F cap a s hc ha hs hsc hstep n x).trans
    (hanti target (min cap (s*a^n)) (le_min htc ht) x)

theorem ten_clock_growth (q : ℕ) (hq : 0 < q) (c : ℝ) (hc : 0 ≤ c) :
    1+10*c ≤ (1+c/(q:ℝ))^(10*q) := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have h := one_add_mul_le_pow (show (-2:ℝ) ≤ c/(q:ℝ) by
    have hd := div_nonneg hc hq'.le
    linarith) (10*q)
  have he : ((10*q:ℕ):ℝ)*(c/(q:ℝ)) = 10*c := by push_cast; field_simp
  rwa [he] at h

theorem ninety_clock_growth (q : ℕ) (hq : 0 < q) :
    (2000:ℝ) ≤ (1+(3/20)/(q:ℝ))^(90*q) := by
  have h := ten_clock_growth q hq (3/20) (by norm_num)
  norm_num at h
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5/2) h 9
  have he : 90*q = (10*q)*9 := by omega
  rw [he,pow_mul]
  norm_num at hp
  linarith

end
end RandomViability.Binding
