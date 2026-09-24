import Mathlib
namespace PhenotypeMemory
theorem quadratic_secant (x y : ℝ) : x^2-y^2=(x+y)*(x-y) := by ring
theorem covariance_forcing (t paired marginal : ℝ) :
    t*paired-t*marginal^2=t*(paired-marginal^2) := by ring
/-- Positive weighted norm comparison, after bounding the source Jacobian. -/
theorem response_bound (h delta k : ℝ) (hk : k < 1)
    (hh : h ≤ delta+k*h) : h ≤ delta/(1-k) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-k)).2
  nlinarith
theorem regularity_response (h t L N k : ℝ) (hN : 0 < N) (hk : k < 1)
    (hh : h ≤ t*(L^2/(4*N))+k*h) :
    h ≤ (t*L^2)/(4*N*(1-k)) := by
  have bound := response_bound h (t*(L^2/(4*N))) k hk hh
  convert bound using 1
  field_simp
theorem comparison_iteration {α : Type*} [Preorder α] (F G : α → α)
    (mono : Monotone G) (hFG : ∀ x, F x ≤ G x) (z : α) :
    ∀ n : ℕ, F^[n] z ≤ G^[n] z := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using (hFG (F^[n] z)).trans (mono ih)
end PhenotypeMemory
