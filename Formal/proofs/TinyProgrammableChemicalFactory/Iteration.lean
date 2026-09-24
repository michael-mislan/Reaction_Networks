import Mathlib

namespace TinyProgrammableChemicalFactory

/-- p n is the probability of joint success through n inspected divisions.
The recurrence is conditional-on-history, not independence. -/
theorem conditional_iteration (p : ℕ → ℝ) (q : ℝ) (hq : 0≤q)
    (h0 : p 0=1) (hstep : ∀ n, q*p n≤p (n+1)) (n : ℕ) : q^n≤p n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    calc
      q^(n+1)=q*q^n := by rw [pow_succ]; ring
      _≤q*p n := mul_le_mul_of_nonneg_left ih hq
      _≤p (n+1) := hstep n

end TinyProgrammableChemicalFactory
