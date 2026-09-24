import proofs.CoreCouplingCAC.Source

namespace CoreCouplingCAC

/-- A quadratic with nonnegative leading and positive linear coefficient
is injective on the positive half-line. -/
theorem positive_quadratic_injective (α β γ x y : ℝ)
    (ha : 0 ≤ α) (hb : 0 < β) (hx : 0 < x) (hy : 0 < y)
    (h₁ : α*x^2+β*x-γ = 0) (h₂ : α*y^2+β*y-γ = 0) : x = y := by
  have hf : (x-y)*(α*(x+y)+β) = 0 := by nlinarith [h₁,h₂]
  have hp : 0 < α*(x+y)+β := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (ne_of_gt hp))

theorem ab_stationary_quadratic (p : Rates) (A B z : ℝ)
    (ha : fA p A B z = 0) (hb : fB p A B z = 0) :
    p.e*(2+z)*A^2+(2+z)*A-
      (p.a*(1+z+p.e)+(z+2*p.e)*p.b) = 0 := by
  dsimp [fA] at ha
  dsimp [fB] at hb
  linear_combination -(1+z+p.e)*ha-(z+2*p.e)*hb

/-- The AB module keeps the same reservoirs and rates and clamps only z.
Uniform uniqueness holds for every positive fixed external concentration.
-/
theorem isolated_AB_unistationary (p : Rates) (hp : 0 ≤ p.e)
    (z A B C D : ℝ) (hz : 0 < z) (hA : 0 < A) (hC : 0 < C)
    (ha : fA p A B z = 0) (hb : fB p A B z = 0)
    (hc : fA p C D z = 0) (hd : fB p C D z = 0) :
    A = C ∧ B = D := by
  have he : A = C := positive_quadratic_injective
    (p.e*(2+z)) (2+z) (p.a*(1+z+p.e)+(z+2*p.e)*p.b) A C
    (by positivity) (by positivity) hA hC
    (ab_stationary_quadratic p A B z ha hb)
    (ab_stationary_quadratic p C D z hc hd)
  refine ⟨he, ?_⟩
  dsimp [fB] at hb hd
  rw [← he] at hd
  have hh : (1+z+p.e)*(B-D) = 0 := by nlinarith [hb,hd]
  have hp' : 0 < 1+z+p.e := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt hp'))

theorem zh_stationary_quadratic (p : Rates) (A B z H : ℝ)
    (hz : fZ p A B z H = 0) (hh : fH p z H = 0) :
    p.v*(1+2*p.d)*z^2+((2+p.d)*B-p.u*(1-p.d))*z-(2+p.d)*A = 0 := by
  dsimp [fZ] at hz
  dsimp [fH] at hh
  linear_combination -(2+p.d)*hz-3*hh

/-- Positive constant term of a concave quadratic gives at most one positive zero,
even when its linear coefficient has either sign. -/
theorem quadratic_one_positive_root (α β γ x y : ℝ)
    (ha : 0 < α) (hg : 0 < γ) (hx : 0 < x) (hy : 0 < y)
    (h₁ : α*x^2+β*x-γ = 0) (h₂ : α*y^2+β*y-γ = 0) : x = y := by
  have hf : (x-y)*(α*(x+y)+β) = 0 := by nlinarith [h₁,h₂]
  rcases mul_eq_zero.mp hf with he | he
  · exact sub_eq_zero.mp he
  · have hbad : α*x*y+γ = 0 := by nlinarith [h₁, he]
    have : 0 < α*x*y+γ := by positivity
    linarith

theorem isolated_ZH_unistationary (p : Rates) (hv : 0 < p.v) (hd : 0 ≤ p.d)
    (A B z H w K : ℝ) (ha : 0 < A) (hz : 0 < z) (hw : 0 < w)
    (hz₁ : fZ p A B z H = 0) (hh₁ : fH p z H = 0)
    (hz₂ : fZ p A B w K = 0) (hh₂ : fH p w K = 0) :
    z = w ∧ H = K := by
  have he : z = w := quadratic_one_positive_root
    (p.v*(1+2*p.d)) ((2+p.d)*B-p.u*(1-p.d)) ((2+p.d)*A) z w
    (by positivity) (by positivity) hz hw
    (zh_stationary_quadratic p A B z H hz₁ hh₁)
    (zh_stationary_quadratic p A B w K hz₂ hh₂)
  refine ⟨he, ?_⟩
  dsimp [fH] at hh₁ hh₂
  rw [← he] at hh₂
  have he' : (2+p.d)*(H-K) = 0 := by nlinarith [hh₁,hh₂]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_left (by positivity))

end CoreCouplingCAC
