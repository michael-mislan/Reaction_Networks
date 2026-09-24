import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

namespace CompositionalMemory
open Polynomial

/-- Semantic rational Chebyshev construction; list arithmetic supplies replay. -/
noncomputable def rationalChebyshevPair : ℕ → Polynomial ℚ × Polynomial ℚ
  | 0 => (1,X)
  | n+1 => let p := rationalChebyshevPair n; (p.2,2*X*p.2-p.1)

noncomputable def rationalChebyshev (n : ℕ) : Polynomial ℚ := (rationalChebyshevPair n).1

theorem rationalChebyshevPair_eq (n : ℕ) :
    rationalChebyshevPair n=(Chebyshev.T ℚ (n : ℤ),Chebyshev.T ℚ ((n : ℤ)+1)) := by
  induction n with
  | zero => simp [rationalChebyshevPair,Chebyshev.T_zero,Chebyshev.T_one]
  | succ n ih =>
    simp only [rationalChebyshevPair,ih,Nat.cast_add,Nat.cast_one]
    rw [show (n : ℤ)+1+1=(n : ℤ)+2 by ring,Chebyshev.T_add_two]

theorem rationalChebyshev_eq (n : ℕ) : rationalChebyshev n=Chebyshev.T ℚ (n : ℤ) := by
  rw [rationalChebyshev,rationalChebyshevPair_eq]

noncomputable def rationalChebyshevPolynomial {N : ℕ} (c : Fin N → ℚ) : Polynomial ℚ :=
  ∑ i,C (c i)*rationalChebyshev i.val

theorem rationalChebyshevPolynomial_eval {N : ℕ} (c : Fin N → ℚ) (x : ℝ) :
    aeval x (rationalChebyshevPolynomial c)=
      ∑ i,(c i : ℝ)*(Chebyshev.T ℝ (i.val : ℤ)).eval x := by
  simp only [rationalChebyshevPolynomial,map_sum,map_mul,aeval_C,rationalChebyshev_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [aeval_def,eval₂_eq_eval_map,Chebyshev.map_T]
  simp

theorem chebyshev_abs_le_one (n : ℕ) (x : ℝ) (hl : -1 ≤ x) (hu : x ≤ 1) :
    |(Chebyshev.T ℝ (n : ℤ)).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hl hu, Chebyshev.T_real_cos]
  exact abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩

/-- Coefficient norm enclosure used by the rational time witnesses. -/
theorem chebyshev_sum_abs_le {N : ℕ} (c : Fin N → ℝ) (x : ℝ)
    (hl : -1 ≤ x) (hu : x ≤ 1) :
    |∑ i,c i*(Chebyshev.T ℝ (i.val : ℤ)).eval x| ≤ ∑ i,|c i| := by
  calc
    _ ≤ ∑ i,|c i*(Chebyshev.T ℝ (i.val : ℤ)).eval x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (chebyshev_abs_le_one i.val x hl hu) (abs_nonneg (c i))

theorem chebyshev_sum_lower {N : ℕ} (c : Fin N → ℝ) (c0 x : ℝ)
    (hl : -1 ≤ x) (hu : x ≤ 1) :
    c0-∑ i,|c i| ≤ c0+∑ i,c i*(Chebyshev.T ℝ (i.val : ℤ)).eval x := by
  have h := (abs_le.mp (chebyshev_sum_abs_le c x hl hu)).1
  linarith

theorem rationalChebyshevPolynomial_abs_bound {N : ℕ} (c : Fin N → ℚ) (B : ℚ)
    (hB : ∑ i,|c i| ≤ B) (x : ℝ) (hl : -1 ≤ x) (hu : x ≤ 1) :
    |aeval x (rationalChebyshevPolynomial c)| ≤ (B : ℝ) := by
  rw [rationalChebyshevPolynomial_eval]
  apply (chebyshev_sum_abs_le (fun i => (c i : ℝ)) x hl hu).trans
  exact_mod_cast hB

end CompositionalMemory
