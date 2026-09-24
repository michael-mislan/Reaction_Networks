import proofs.CompositionalMemory.Scaling
import Mathlib.Algebra.BigOperators.Field

namespace CompositionalMemory
open Finset

theorem membrane_first_moment {k : ℕ} (hk : 1 ≤ k) (i : Fin k)
    (z : Fin k → ℝ) (γ m U Z : ℝ)
    (hγ : 0 ≤ γ) (hm : 0 < m) (hU : 0 ≤ U) (hZ : 0 ≤ Z)
    (hz : ∀ j, z j ≤ Z) :
    ∑ j, (γ*(m/k)*z j)*((U+if j=i then (k : ℝ) else 0)/(m+1)) ≤
      γ*Z*(U+1) := by
  classical
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpoint (j : Fin k) :
      (γ*(m/k)*z j)*((U+if j=i then (k : ℝ) else 0)/(m+1)) =
      (γ*m/((k : ℝ)*(m+1)))*(U*z j+if j=i then (k : ℝ)*z i else 0) := by
    by_cases h : j=i
    · subst j; simp; field_simp
    · simp [h]; field_simp
  have hs : ∑ j, z j ≤ (k : ℝ)*Z := by
    calc
      _ ≤ ∑ _j : Fin k, Z := sum_le_sum (fun j _ => hz j)
      _ = _ := by simp
  have hb : U*(∑ j, z j)+(k : ℝ)*z i ≤ (k : ℝ)*Z*(U+1) := by
    have h1 := mul_le_mul_of_nonneg_left hs hU
    have h2 := mul_le_mul_of_nonneg_left (hz i) hkpos.le
    nlinarith only [h1,h2]
  simp_rw [hpoint]
  rw [← mul_sum, sum_add_distrib, ← mul_sum]
  simp only [sum_ite_eq',mem_univ,ite_true]
  calc
    _ ≤ (γ*m/((k : ℝ)*(m+1)))*((k : ℝ)*Z*(U+1)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = γ*Z*(U+1)*(m/(m+1)) := by field_simp
    _ ≤ γ*Z*(U+1)*1 := mul_le_mul_of_nonneg_left
      ((div_le_one (show 0 < m+1 by positivity)).mpr (by linarith)) (by positivity)
    _ = _ := by ring

theorem membrane_jump_size {k : ℕ} (hk : 1 ≤ k) (i j : Fin k)
    (m N U : ℝ) (hN : 0 < N) (hm : (k : ℝ)*N ≤ m) (hU : 0 ≤ U) :
    (U+if j=i then (k : ℝ) else 0)/(m+1) ≤ (U+1)/N := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmpos : 0 < m := by nlinarith only [hm,hk1,hN]
  apply (div_le_div_iff₀ (by positivity : 0 < m+1) hN).mpr
  have hUk := mul_nonneg (sub_nonneg.mpr hk1) hU
  have hNU := mul_le_mul_of_nonneg_right hm (show 0 ≤ U+1 by positivity)
  split_ifs <;> nlinarith only [hNU,mul_nonneg hN.le hUk,hN,hU,mul_nonneg hN.le hU]

/-- The consuming channel is counted once; all other channels only dilute. -/
theorem consuming_sum_identity {k : ℕ} (i : Fin k) (z : Fin k → ℝ) (U : ℝ) :
    ∑ j, z j*(U+if j=i then (k : ℝ) else 0)^2 =
      U^2*(∑ j, z j)+(2*U*k+(k : ℝ)^2)*z i := by
  classical
  have hpoint (j : Fin k) : z j*(U+if j=i then (k : ℝ) else 0)^2 =
      U^2*z j+if j=i then (2*U*k+(k : ℝ)^2)*z i else 0 := by
    by_cases h : j=i
    · subst j; simp; ring
    · simp [h]; ring
  simp_rw [hpoint]
  rw [sum_add_distrib, ← mul_sum]
  simp

/-- Exact rate-weighted sum of squared upper bounds on the membrane jumps. -/
theorem membrane_moment_identity {k : ℕ} (hk : 1 ≤ k) (i : Fin k)
    (z : Fin k → ℝ) (γ m U : ℝ) (hm : 0 < m) :
    ∑ j, (γ*(m/k)*z j)*((U+if j=i then (k : ℝ) else 0)/(m+1))^2 =
      γ*m/((k : ℝ)*(m+1)^2)*
        (U^2*(∑ j, z j)+(2*U*k+(k : ℝ)^2)*z i) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hm0 : m+1 ≠ 0 := by positivity
  rw [← consuming_sum_identity i z U, mul_sum]
  apply sum_congr rfl
  intro j _
  field_simp [hk0,hm0]

theorem membrane_moment_uniform {k : ℕ} (hk : 1 ≤ k) (i : Fin k)
    (z : Fin k → ℝ) (γ m N U Z : ℝ)
    (hγ : 0 ≤ γ) (hN : 0 < N) (hm : (k : ℝ)*N ≤ m)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hz : ∀ j, z j ≤ Z) :
    ∑ j, (γ*(m/k)*z j)*((U+if j=i then (k : ℝ) else 0)/(m+1))^2 ≤
      γ*Z*(U+1)^2/N := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith only [hk1]
  have hmpos : 0 < m := lt_of_lt_of_le (mul_pos hkpos hN) hm
  have hs : ∑ j, z j ≤ (k : ℝ)*Z := by
    calc
      _ ≤ ∑ _j : Fin k, Z := sum_le_sum (fun j _ => hz j)
      _ = _ := by simp
  have hbracket : U^2*(∑ j, z j)+(2*U*k+(k : ℝ)^2)*z i ≤
      (k : ℝ)*Z*(U^2+2*U+k) := by
    have h1 := mul_le_mul_of_nonneg_left hs (sq_nonneg U)
    have h2 := mul_le_mul_of_nonneg_left (hz i)
      (show 0 ≤ 2*U*k+(k : ℝ)^2 by positivity)
    nlinarith only [h1,h2]
  rw [membrane_moment_identity hk i z γ m U hmpos]
  calc
    _ ≤ γ*m/((k : ℝ)*(m+1)^2)*((k : ℝ)*Z*(U^2+2*U+k)) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = γ*Z*(m/(m+1)^2*(U^2+2*U+k)) := by
      field_simp
    _ ≤ γ*Z*((U+1)^2/N) := mul_le_mul_of_nonneg_left
      (membrane_second_moment_scalar k m N U hk1 hN hm hU) (mul_nonneg hγ hZ)
    _ = _ := by ring

end CompositionalMemory
