import Mathlib

noncomputable section
namespace OverlappingSiphonInvasion

def siphonProduct (a b c : ℝ) : ℝ := (a+c)*(b+2*c)

/-- Derivative of P plus the bounded susceptible correction, for the fixed
positive-rate witness. Connection to literal field is proved separately. -/
def correctedProductDrift (s a b c : ℝ) : ℝ :=
  (a*(2*s+b/10-1)+c*(11*s/10+b/10-1))*(b+2*c) +
  (a+c)*(b*(s+3*a/10-1)+2*c*(3*s/2+a/10-1+b/20)) +
  (4-s*(1+2*a+b+21*c/10))*siphonProduct a b c/2

def boundarySquares (s a b c : ℝ) : ℝ :=
  a^2*b*(s-9/10)^2 + 2*a^2*c*(s-11/20)^2 +
  a*b^2*(s+2/5)^2/2 + b^2*c*(s-1/2)^2/2

def positiveRemainder (a b c : ℝ) : ℝ :=
    (61/20:ℝ) * a^3 * b^1 * c^1 +
    (41/10:ℝ) * a^3 * c^2 +
    (61/10:ℝ) * a^2 * b^2 * c^1 +
    14 * a^2 * b^2 +
    (327/20:ℝ) * a^2 * b^1 * c^2 +
    (343/10:ℝ) * a^2 * b^1 * c^1 +
    (17/50:ℝ) * a^2 * b^1 +
    (103/10:ℝ) * a^2 * c^3 +
    (148/5:ℝ) * a^2 * c^2 +
    (19/200:ℝ) * a^2 * c^1 +
    (61/20:ℝ) * a^1 * b^3 * c^1 +
    (143/10:ℝ) * a^1 * b^2 * c^2 +
    (63/10:ℝ) * a^1 * b^2 * c^1 +
    (27/100:ℝ) * a^1 * b^2 +
    (391/20:ℝ) * a^1 * b^1 * c^3 +
    (251/5:ℝ) * a^1 * b^1 * c^2 +
    (201/5:ℝ) * a^1 * b^1 * c^1 +
    (83/10:ℝ) * a^1 * c^4 +
    73 * a^1 * c^3 +
    (203/5:ℝ) * a^1 * c^2 +
    (41/20:ℝ) * b^3 * c^2 +
    (31/5:ℝ) * b^2 * c^3 +
    (3/10:ℝ) * b^2 * c^2 +
    (9/40:ℝ) * b^2 * c^1 +
    (25/4:ℝ) * b^1 * c^4 +
    (297/10:ℝ) * b^1 * c^3 +
    (461/20:ℝ) * b^1 * c^2 +
    (21/10:ℝ) * c^5 +
    (217/5:ℝ) * c^4 +
    (167/10:ℝ) * c^3

theorem square_certificate_identity (a b c : ℝ) :
    (a+b+c)*(correctedProductDrift (4-a-b-c) a b c-siphonProduct a b c/20) +
      14*(siphonProduct a b c)^2 =
    boundarySquares (4-a-b-c) a b c + positiveRemainder a b c := by
  unfold correctedProductDrift siphonProduct boundarySquares positiveRemainder
  ring

theorem square_certificate_nonneg (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ (a+b+c)*(correctedProductDrift (4-a-b-c) a b c-siphonProduct a b c/20) +
      14*(siphonProduct a b c)^2 := by
  rw [square_certificate_identity]
  unfold boundarySquares positiveRemainder
  positivity

theorem virtual_corrected_logistic (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hI : 1 ≤ a+b+c) :
    siphonProduct a b c*(1/20-14*siphonProduct a b c) ≤
      correctedProductDrift (4-a-b-c) a b c := by
  have h := square_certificate_nonneg a b c ha hb hc
  have hsq : 0 ≤ (siphonProduct a b c)^2 := sq_nonneg _
  have hmul := mul_nonneg (sub_nonneg.mpr hI) hsq
  have hIpos : 0 < a+b+c := by linarith
  by_contra hn
  have hbad := mul_pos hIpos (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [h, hmul, hbad]

/-- Dependence on susceptible abundance is affine, including the correction. -/
def susceptibleCoefficient (a b c : ℝ) : ℝ :=
  (2*a+11*c/10)*(b+2*c)+(a+c)*(b+3*c) -
    (1+2*a+b+21*c/10)*siphonProduct a b c/2

theorem susceptible_shift (s t a b c : ℝ) :
    correctedProductDrift s a b c - correctedProductDrift t a b c =
      (s-t)*susceptibleCoefficient a b c := by
  unfold correctedProductDrift susceptibleCoefficient siphonProduct
  ring

theorem susceptible_coefficient_bound (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hI : a+b+c ≤ 5) :
    |susceptibleCoefficient a b c| ≤ 10*siphonProduct a b c := by
  have hu : 0 ≤ a+c := by positivity
  have hv : 0 ≤ b+2*c := by positivity
  have hP : 0 ≤ siphonProduct a b c := mul_nonneg hu hv
  have h1 : 0 ≤ (2*a+11*c/10)*(b+2*c) := by positivity
  have h2 : 0 ≤ (a+c)*(b+3*c) := by positivity
  have h1u : (2*a+11*c/10)*(b+2*c) ≤ 2*siphonProduct a b c := by
    dsimp [siphonProduct]
    nlinarith only [mul_nonneg hc hv]
  have h2u : (a+c)*(b+3*c) ≤ 3/2*siphonProduct a b c := by
    dsimp [siphonProduct]
    nlinarith only [mul_nonneg hu hb]
  have hl : 0 ≤ 1+2*a+b+21*c/10 := by positivity
  have hlu : 1+2*a+b+21*c/10 ≤ 12 := by linarith
  have hlp := mul_nonneg hl hP
  have hlpu := mul_le_mul_of_nonneg_right hlu hP
  rw [abs_le]
  dsimp [susceptibleCoefficient]
  constructor <;> nlinarith only [h1,h2,h1u,h2u,hlp,hlpu,hP]

/-- A genuine interior drift bound: approximate total population is sufficient;
the exact limiting simplex is not assumed. -/
theorem corrected_logistic (s a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hI : 1 ≤ a+b+c) (hIu : a+b+c ≤ 5)
    (hN : |s+a+b+c-4| ≤ 1/1000) :
    siphonProduct a b c*(1/25-14*siphonProduct a b c) ≤
      correctedProductDrift s a b c := by
  have hbase := virtual_corrected_logistic a b c ha hb hc hI
  have hP : 0 ≤ siphonProduct a b c := by unfold siphonProduct; positivity
  have hcoef := susceptible_coefficient_bound a b c ha hb hc hIu
  have herr : |s-(4-a-b-c)| ≤ 1/1000 := by
    convert hN using 1
    congr 1
    ring
  have hprod := mul_le_mul herr hcoef (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/1000)
  rw [← abs_mul, ← susceptible_shift] at hprod
  have hlow := (abs_le.mp hprod).1
  nlinarith only [hbase,hlow]

end OverlappingSiphonInvasion
