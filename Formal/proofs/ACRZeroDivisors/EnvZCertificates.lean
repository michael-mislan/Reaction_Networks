import Mathlib.Tactic

namespace ACRZeroDivisors

/-- Nine fluxes in the source paper's forward/backward/catalytic order. -/
def envZFlux (k : Fin 9 → ℝ) (x : Fin 7 → ℝ) : Fin 9 → ℝ :=
  ![k 0*x 0, k 1*x 1, k 2*x 1, k 3*x 2*x 3, k 4*x 5,
    k 5*x 5, k 6*x 1*x 4, k 7*x 6, k 8*x 6]

/-- Stoichiometric changes of X⇌XT→Xp, Xp+Y⇌XpY→X+Yp,
and XT+Yp⇌XTYp→XT+Y. -/
def envZField (k : Fin 9 → ℝ) (x : Fin 7 → ℝ) : Fin 7 → ℝ :=
  let v := envZFlux k x
  ![-v 0+v 1+v 5, v 0-v 1-v 2-v 6+v 7+v 8,
    v 2-v 3+v 4, -v 3+v 4+v 8, v 5-v 6+v 7,
    v 3-v 4-v 5, v 6-v 7-v 8]

theorem envZ_identities (k : Fin 9 → ℝ) (x : Fin 7 → ℝ) :
    k 8*envZField k x 6-(k 7+k 8)*(envZField k x 2-envZField k x 3) =
      x 1*(k 6*k 8*x 4-k 2*(k 7+k 8)) ∧
    k 2*envZField k x 6-k 6*x 4*(envZField k x 2-envZField k x 3) =
      x 6*(k 6*k 8*x 4-k 2*(k 7+k 8)) := by
  simp [envZField, envZFlux]
  constructor <;> ring

theorem envZ_conservation (k : Fin 9 → ℝ) (x : Fin 7 → ℝ) :
    envZField k x 0+envZField k x 1+envZField k x 2+envZField k x 5+envZField k x 6=0 ∧
    envZField k x 3+envZField k x 4+envZField k x 5+envZField k x 6=0 := by
  simp [envZField, envZFlux]
  constructor <;> ring

theorem envZ_reconstruction (k : Fin 9 → ℝ) (t y : ℝ)
    (hk : ∀ i, k i ≠ 0) (hy : y ≠ 0) :
    ∀ i, envZField k ![(k 1+k 2)/k 0*t, t,
      ((k 4+k 5)*k 2/(k 3*k 5))*t/y, y,
      k 2*(k 7+k 8)/(k 6*k 8), k 2/k 5*t, k 2/k 8*t] i=0 := by
  intro i
  fin_cases i <;> simp [envZField, envZFlux] <;> field_simp [hk] <;> ring

theorem envZ_pool_reduction (L C K X U y : ℝ) (hh : L*y+C ≠ 0) :
    y+K*(X*y/(L*y+C))=U ↔
    L*y^2+(C+K*X-L*U)*y-C*U=0 := by
  have he : (y+K*(X*y/(L*y+C))-U)*(L*y+C) =
      L*y^2+(C+K*X-L*U)*y-C*U := by
    calc
      _ = (y-U)*(L*y+C)+K*((X*y/(L*y+C))*(L*y+C)) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hh]; ring
  rw [← he, mul_eq_zero, or_iff_left hh, sub_eq_zero]

end ACRZeroDivisors
