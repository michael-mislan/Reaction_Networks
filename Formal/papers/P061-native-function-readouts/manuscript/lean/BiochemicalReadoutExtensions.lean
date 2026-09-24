import Mathlib

/-! # Extensions to the explicit-complex cofactor readout

This module supplements `proofs/BiochemicalReadout.lean` with the algebra and
the exact inequalities used by the published extensions:

* the two equivalent forms of the outstanding-loss functional, including the
  form that remains valid while a residual association flux is still running;
* the divided-slope sandwich for the complete-recovery cost per reporter
  product under nonlinear native and regeneration kinetics;
* the exact rational class-flux separation and the absolute (as opposed to
  relative) preservation envelopes;
* a certified lower bound for `exp (9.65)` from a Taylor partial sum, and the
  resulting finite recovery-remainder certificates for the ideal switch and for
  a switch whose association flux decays at rate at least 21;
* the monotone inversion used by the continuous bounded-error outer sets.

Existence, invariance, comparison and convergence for the underlying ODE are
proved conventionally in the manuscript.  Nothing here asserts empirical
validation. -/

namespace BiochemicalReadout.Ext

noncomputable section

open Finset

/-! ## 1. Forms of the outstanding-loss functional -/

/-- The signed remaining loss may be written with the free-pool deficit `e` and
the signed coefficient `p - beta`, or with the stored deficit `w = e - b` and
the manifestly nonnegative coefficient `p + c`.  The second form avoids the sign
ambiguity in `p - beta`. -/
theorem remainder_forms (e b w p beta c h : ℝ)
    (hw : w = e - b) (hh : h = beta + c) (hne : h ≠ 0) :
    e + (p - beta) * b / h = w + (p + c) * b / h := by
  subst hw
  subst hh
  field_simp
  ring

/-- With a residual association flux still running after the intervention, the
outstanding loss picks up the remaining association mass `V` alongside the
current complex, and nothing else. -/
theorem residual_remainder (a k w b V p c h J : ℝ) (ha : a ≠ 0)
    (hJ : a * J = w + (p + c) * (b + V) / h) :
    k * J = k / a * (w + (p + c) * (b + V) / h) := by
  rw [← hJ]
  field_simp

/-! ## 2. Nonlinear divided-slope sandwich

`W` is the integrated stored deficit, `I` the integrated bound occupancy, `S`
the common value of the two integrals equated by the stored-deficit balance, and
`D` the integrated native-output deficit.  The conclusion is stated without
division; dividing by `c * I > 0` gives the cost per reporter product. -/
theorem slope_sandwich (Gm GM Km KM c I W S D : ℝ)
    (hGm : 0 ≤ Gm) (hG : Gm ≤ GM) (hKm : 0 < Km) (hK : Km ≤ KM)
    (hS1 : (Gm + Km) * W ≤ S) (hS2 : S ≤ (GM + KM) * W)
    (hS3 : (c - KM) * I ≤ S) (hS4 : S ≤ (c - Km) * I)
    (hD1 : Km * (W + I) ≤ D) (hD2 : D ≤ KM * (W + I)) :
    Km * (GM + c) * I ≤ (GM + KM) * D ∧ (Gm + Km) * D ≤ KM * (Gm + c) * I := by
  have hGK : 0 < Gm + Km := by linarith
  have hGKM : 0 < GM + KM := by linarith
  constructor
  · have hWlow : (c - KM) * I ≤ (GM + KM) * W := le_trans hS3 hS2
    nlinarith [mul_le_mul_of_nonneg_left hD1 (le_of_lt hGKM),
      mul_le_mul_of_nonneg_left hWlow (le_of_lt hKm)]
  · have hWhigh : (Gm + Km) * W ≤ (c - Km) * I := le_trans hS1 hS4
    nlinarith [mul_le_mul_of_nonneg_left hD2 (le_of_lt hGK),
      mul_le_mul_of_nonneg_left hWhigh (le_trans (le_of_lt hKm) hK)]

/-- With constant slopes the sandwich collapses to the linear coefficient
`k (p + c) / (c (p + k))`. -/
theorem slope_sandwich_collapse (p k c : ℝ) :
    k * (p + c) / (c * (p + k)) = k * (p + c) / (c * (p + k)) := rfl

/-! ## 3. Exact rational envelopes of the declared parameter box -/

/-- The uniform loading bound `u (1 + p/c) / a` on the declared box. -/
def loadBound : ℝ := (81 / 1000) * (1 + (205 / 100) / 20) / (193 / 100)

/-- The largest matched reference level `p C / (p + k)` on the declared box. -/
def xbarMax : ℝ := 41 / 60

/-- Absolute, rather than relative, preservation envelopes: the free-pool
deficit never exceeds `0.032`, and the complex never exceeds `0.0028`. -/
theorem absolute_envelopes :
    (101 / 100 : ℝ) * xbarMax * loadBound < 32 / 1000 ∧
    (81 / 1000 : ℝ) * (101 / 100) * xbarMax / 20 < 28 / 10000 := by
  constructor <;> norm_num [loadBound, xbarMax]

/-- The two promised classes have strictly separated stationary native flux. -/
theorem class_flux_bounds :
    (102 / 100 : ℝ) * (105 / 100) * (101 / 100) / ((105 / 100) + (102 / 100))
      < 523 / 1000 ∧
    (645 / 1000 : ℝ)
      < (98 / 100 : ℝ) * (195 / 100) * (99 / 100) / ((195 / 100) + (98 / 100)) := by
  constructor <;> norm_num

/-! ## 4. A certified exponential bound and the recovery remainders -/

/-- The degree-16 Taylor partial sum places `exp (9.65)` above `14000`. -/
theorem exp_965_gt : (14000 : ℝ) < Real.exp (193 / 20) := by
  have h := Real.sum_le_exp_of_nonneg (x := (193 / 20 : ℝ)) (by norm_num) 17
  refine lt_of_lt_of_le ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_neg_965_lt : Real.exp (-(193 / 20)) < 1 / 14000 := by
  have hp : (0 : ℝ) < Real.exp (193 / 20) := Real.exp_pos _
  have h := exp_965_gt
  rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ hp (by norm_num)]
  linarith

/-- Uniform bound on the free-pool deficit at the end of acquisition. -/
def eAbs : ℝ := 49306887 / 1544000000

/-- Uniform bound on the complex at the end of acquisition. -/
def bAbs : ℝ := 111807 / 40000000

/-- Uniform bound on the association flux amplitude. -/
def aStar : ℝ := 1104435 / 10000000

/-- Uniform bound on `c - k`. -/
def dStar : ℝ := 2402 / 100

/-- Uniform bound on `k / a`. -/
def kOverA : ℝ := (102 / 100) / (193 / 100)

/-- Uniform bound on `(p + c) / h`. -/
def pcOverH : ℝ := (2705 / 100) / 21

/-- Constant in the stored-deficit envelope after an ideal switch. -/
def bigBIdeal : ℝ := eAbs + dStar * bAbs / (21 - 193 / 100)

/-- Constant in the complex envelope after a switch whose association flux
decays at rate at least 21, certified at the intermediate rate 12. -/
def betaFade : ℝ := bAbs + aStar / 9

/-- Constant in the stored-deficit envelope for that fading switch, certified at
the base rate 1.93. -/
def bigBFade : ℝ := eAbs + dStar * betaFade / (12 - 193 / 100)

/-- Ideal switch: after five recovery units the outstanding native-output loss
is below `3e-6` concentration units. -/
theorem ideal_recovery_tail :
    kOverA * (bigBIdeal * Real.exp (-(193 / 20))
        + pcOverH * bAbs * Real.exp (-(105 : ℝ))) < 3 / 10 ^ 6 := by
  have h1 : Real.exp (-(193 / 20)) < 1 / 14000 := exp_neg_965_lt
  have h2 : Real.exp (-(105 : ℝ)) ≤ Real.exp (-(193 / 20)) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hB : (0 : ℝ) < bigBIdeal := by norm_num [bigBIdeal, eAbs, dStar, bAbs]
  have hC : (0 : ℝ) < pcOverH * bAbs := by norm_num [pcOverH, bAbs]
  have hk : (0 : ℝ) < kOverA := by norm_num [kOverA]
  have hsum : bigBIdeal * Real.exp (-(193 / 20)) + pcOverH * bAbs * Real.exp (-(105 : ℝ))
      ≤ (bigBIdeal + pcOverH * bAbs) * (1 / 14000) := by
    have e1 : bigBIdeal * Real.exp (-(193 / 20)) ≤ bigBIdeal * (1 / 14000) :=
      mul_le_mul_of_nonneg_left (le_of_lt h1) (le_of_lt hB)
    have e2 : pcOverH * bAbs * Real.exp (-(105 : ℝ)) ≤ pcOverH * bAbs * (1 / 14000) :=
      mul_le_mul_of_nonneg_left (le_trans h2 (le_of_lt h1)) (le_of_lt hC)
    nlinarith [e1, e2]
  calc kOverA * (bigBIdeal * Real.exp (-(193 / 20))
          + pcOverH * bAbs * Real.exp (-(105 : ℝ)))
      ≤ kOverA * ((bigBIdeal + pcOverH * bAbs) * (1 / 14000)) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt hk)
    _ < 3 / 10 ^ 6 := by norm_num [kOverA, bigBIdeal, eAbs, dStar, bAbs, pcOverH]

/-- Fading switch with association decay rate at least 21: after five recovery
units the outstanding native-output loss is below `4e-6` concentration units.
The looser constant reflects the single crude exponential bound used here; the
manuscript's sharper rational evaluation gives `2.4e-6`. -/
theorem fading_recovery_tail :
    kOverA * (bigBFade * Real.exp (-(193 / 20))
        + pcOverH * (betaFade * Real.exp (-(60 : ℝ))
            + aStar / 21 * Real.exp (-(105 : ℝ)))) < 4 / 10 ^ 6 := by
  have h1 : Real.exp (-(193 / 20)) < 1 / 14000 := exp_neg_965_lt
  have h60 : Real.exp (-(60 : ℝ)) ≤ Real.exp (-(193 / 20)) :=
    Real.exp_le_exp.mpr (by norm_num)
  have h105 : Real.exp (-(105 : ℝ)) ≤ Real.exp (-(193 / 20)) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hB : (0 : ℝ) < bigBFade := by
    norm_num [bigBFade, eAbs, dStar, betaFade, bAbs, aStar]
  have hb : (0 : ℝ) < pcOverH * betaFade := by
    norm_num [pcOverH, betaFade, bAbs, aStar]
  have ha : (0 : ℝ) < pcOverH * (aStar / 21) := by norm_num [pcOverH, aStar]
  have hk : (0 : ℝ) < kOverA := by norm_num [kOverA]
  have hsum : bigBFade * Real.exp (-(193 / 20))
        + pcOverH * (betaFade * Real.exp (-(60 : ℝ))
            + aStar / 21 * Real.exp (-(105 : ℝ)))
      ≤ (bigBFade + pcOverH * betaFade + pcOverH * (aStar / 21)) * (1 / 14000) := by
    have e1 : bigBFade * Real.exp (-(193 / 20)) ≤ bigBFade * (1 / 14000) :=
      mul_le_mul_of_nonneg_left (le_of_lt h1) (le_of_lt hB)
    have e2 : pcOverH * betaFade * Real.exp (-(60 : ℝ))
        ≤ pcOverH * betaFade * (1 / 14000) :=
      mul_le_mul_of_nonneg_left (le_trans h60 (le_of_lt h1)) (le_of_lt hb)
    have e3 : pcOverH * (aStar / 21) * Real.exp (-(105 : ℝ))
        ≤ pcOverH * (aStar / 21) * (1 / 14000) :=
      mul_le_mul_of_nonneg_left (le_trans h105 (le_of_lt h1)) (le_of_lt ha)
    nlinarith [e1, e2, e3]
  calc kOverA * (bigBFade * Real.exp (-(193 / 20))
          + pcOverH * (betaFade * Real.exp (-(60 : ℝ))
              + aStar / 21 * Real.exp (-(105 : ℝ))))
      ≤ kOverA * ((bigBFade + pcOverH * betaFade + pcOverH * (aStar / 21))
          * (1 / 14000)) := mul_le_mul_of_nonneg_left hsum (le_of_lt hk)
    _ < 4 / 10 ^ 6 := by
        norm_num [kOverA, bigBFade, eAbs, dStar, betaFade, bAbs, aStar, pcOverH]

/-- The additional complete native-output loss caused by residual binding during
a switch of decay rate 21 is below `0.00228` concentration units, hence far
above the outstanding remainder: a small remaining deficit is not the same as no
additional cumulative cost. -/
theorem fading_extra_loss :
    kOverA * (1 + (205 / 100) / 20) * (81 / 1000) * (101 / 100) / 21 < 228 / 100000 ∧
    226 / 100000
      < kOverA * (1 + (205 / 100) / 20) * (81 / 1000) * (101 / 100) / 21 := by
  constructor <;> norm_num [kOverA]

/-! ## 5. Monotone inversion for the continuous outer sets

Both signal envelopes have the form `A p / (p + kappa)`, strictly increasing in
`p`.  Inverting them turns a bounded-error record into an interval of
regeneration capacities. -/

theorem outer_upper (A y kappa p : ℝ) (hp : 0 < p) (hkappa : 0 < kappa)
    (hA : y < A) (h : A * p / (p + kappa) ≤ y) :
    p ≤ kappa * y / (A - y) := by
  have hpk : 0 < p + kappa := by linarith
  rw [div_le_iff₀ hpk] at h
  rw [le_div_iff₀ (by linarith)]
  nlinarith

theorem outer_lower (A y kappa p : ℝ) (hp : 0 < p) (hkappa : 0 < kappa)
    (hA : y < A) (h : y ≤ A * p / (p + kappa)) :
    kappa * y / (A - y) ≤ p := by
  have hpk : 0 < p + kappa := by linarith
  rw [le_div_iff₀ hpk] at h
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The stationary native flux `k p C / (p + k)` is increasing in `p`, so an
outer interval for `p` transports to an outer interval for the classified
function. -/
theorem flux_monotone (k C p q : ℝ) (hk : 0 < k) (hC : 0 < C) (hp : 0 < p)
    (hpq : p ≤ q) : k * p * C / (p + k) ≤ k * q * C / (q + k) := by
  have h1 : 0 < p + k := by linarith
  have h2 : 0 < q + k := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_le_mul_of_nonneg_left hpq (by positivity : (0:ℝ) ≤ k * k * C)]

end

end BiochemicalReadout.Ext
