import Mathlib

/-!
# The normalized two-torus used by the Bressan mixing campaign

This module fixes a single representation and measure normalization.  It does
not assume any mixing estimate.
-/

open MeasureTheory

namespace Bressan

/-- The unit additive circle `ℝ/ℤ`. -/
abbrev T1 := UnitAddCircle

/-- The flat unit two-torus. -/
abbrev T2 := T1 × T1

/-- The Euclidean product geodesic radius on the flat unit two-torus.

The ambient product type carries Lean's maximum product metric, so the
Euclidean radius used by the metric-log potential must be named explicitly. -/
noncomputable def torusEuclideanDist (x y : T2) : ℝ :=
  Real.sqrt (‖x.1 - y.1‖ ^ 2 + ‖x.2 - y.2‖ ^ 2)

theorem continuous_torusEuclideanDist :
    Continuous (Function.uncurry torusEuclideanDist) := by
  unfold torusEuclideanDist Function.uncurry
  fun_prop

theorem torusEuclideanDist_nonneg (x y : T2) :
    0 ≤ torusEuclideanDist x y :=
  Real.sqrt_nonneg _

theorem torusEuclideanDist_self (x : T2) :
    torusEuclideanDist x x = 0 := by
  simp [torusEuclideanDist]

theorem torusEuclideanDist_comm (x y : T2) :
    torusEuclideanDist x y = torusEuclideanDist y x := by
  simp only [torusEuclideanDist, norm_sub_rev]

/-- The named Euclidean torus radius is controlled by the ambient maximum
product metric.  This is the constant needed when a hypothesis is stated
using `Metric.ball` but the matching cost uses `torusEuclideanDist`. -/
theorem torusEuclideanDist_le_sqrt_two_mul_dist (x y : T2) :
    torusEuclideanDist x y ≤ Real.sqrt 2 * dist x y := by
  have h₁ : ‖x.1 - y.1‖ ≤ dist x y := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_left _ _
  have h₂ : ‖x.2 - y.2‖ ≤ dist x y := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_right _ _
  have hsquares :
      ‖x.1 - y.1‖ ^ 2 + ‖x.2 - y.2‖ ^ 2 ≤ 2 * dist x y ^ 2 := by
    nlinarith [norm_nonneg (x.1 - y.1), norm_nonneg (x.2 - y.2),
      (show 0 ≤ dist x y from dist_nonneg)]
  rw [torusEuclideanDist]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith

/-- The ambient maximum product distance is bounded by the named Euclidean
product radius. -/
theorem dist_le_torusEuclideanDist (x y : T2) :
    dist x y ≤ torusEuclideanDist x y := by
  rw [Prod.dist_eq]
  apply max_le
  · rw [dist_eq_norm, torusEuclideanDist]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg ‖x.2 - y.2‖]
  · rw [dist_eq_norm, torusEuclideanDist]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg ‖x.1 - y.1‖]

theorem torusEuclideanDist_le_sqrt_two_div_two (x y : T2) :
    torusEuclideanDist x y ≤ Real.sqrt 2 / 2 := by
  have h₁ : ‖x.1 - y.1‖ ≤ (1 : ℝ) / 2 := by
    simpa using AddCircle.norm_le_half_period (p := (1 : ℝ))
      (x := x.1 - y.1) one_ne_zero
  have h₂ : ‖x.2 - y.2‖ ≤ (1 : ℝ) / 2 := by
    simpa using AddCircle.norm_le_half_period (p := (1 : ℝ))
      (x := x.2 - y.2) one_ne_zero
  have hsquares : ‖x.1 - y.1‖ ^ 2 + ‖x.2 - y.2‖ ^ 2 ≤ (1 : ℝ) / 2 := by
    nlinarith [norm_nonneg (x.1 - y.1), norm_nonneg (x.2 - y.2)]
  have hsqrt := Real.sqrt_le_sqrt hsquares
  have hhalf : Real.sqrt ((1 : ℝ) / 2) = Real.sqrt 2 / 2 := by
    have hleft := Real.sq_sqrt (by positivity : 0 ≤ (1 : ℝ) / 2)
    have hright := Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))
    nlinarith [Real.sqrt_nonneg ((1 : ℝ) / 2), Real.sqrt_nonneg (2 : ℝ)]
  rw [torusEuclideanDist]
  exact hsqrt.trans_eq hhalf

/-- Moving through an antipodal coordinate lowers the Euclidean torus radius
at a definite linear rate.  The rate may depend on the base displacement;
only its positivity is needed to exclude differentiable dual contact. -/
theorem euclideanAntipodal_radius_drop
    {a b t : ℝ} (ha : 0 < a) (ht : |t| ≤ a) :
    a * |t| / (2 * Real.sqrt (a ^ 2 + b ^ 2)) ≤
      Real.sqrt (a ^ 2 + b ^ 2) -
        Real.sqrt ((a - |t|) ^ 2 + b ^ 2) := by
  have hbase : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hshift : 0 ≤ (a - |t|) ^ 2 + b ^ 2 := by positivity
  have hbase_pos : 0 < a ^ 2 + b ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_nonneg b]
  have hroot_pos : 0 < Real.sqrt (a ^ 2 + b ^ 2) :=
    Real.sqrt_pos.2 hbase_pos
  have hradicand_le : (a - |t|) ^ 2 + b ^ 2 ≤ a ^ 2 + b ^ 2 := by
    nlinarith [abs_nonneg t, mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]
  have hroot_le :
      Real.sqrt ((a - |t|) ^ 2 + b ^ 2) ≤
        Real.sqrt (a ^ 2 + b ^ 2) :=
    Real.sqrt_le_sqrt hradicand_le
  have hfactor :
      (Real.sqrt (a ^ 2 + b ^ 2) -
          Real.sqrt ((a - |t|) ^ 2 + b ^ 2)) *
        (Real.sqrt (a ^ 2 + b ^ 2) +
          Real.sqrt ((a - |t|) ^ 2 + b ^ 2)) =
        2 * a * |t| - |t| ^ 2 := by
    calc
      _ = Real.sqrt (a ^ 2 + b ^ 2) ^ 2 -
          Real.sqrt ((a - |t|) ^ 2 + b ^ 2) ^ 2 := by ring
      _ = 2 * a * |t| - |t| ^ 2 := by
        rw [Real.sq_sqrt hbase, Real.sq_sqrt hshift]
        ring
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (a ^ 2 + b ^ 2))).2
  nlinarith [sq_nonneg
    (Real.sqrt (a ^ 2 + b ^ 2) -
      Real.sqrt ((a - |t|) ^ 2 + b ^ 2)),
    mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]

/-- Exact local lift of the antipodal point of the unit additive circle. -/
theorem unitAddCircle_norm_half_add
    {t : ℝ} (ht : |t| ≤ (1 : ℝ) / 2) :
    ‖(((1 : ℝ) / 2 + t : ℝ) : T1)‖ = (1 : ℝ) / 2 - |t| := by
  obtain ⟨htlower, htupper⟩ := abs_le.mp ht
  by_cases htneg : t < 0
  · have hround : round ((1 : ℝ) / 2 + t) = 0 := by
      rw [round_eq_iff]
      constructor <;> norm_num <;> linarith
    rw [UnitAddCircle.norm_eq, hround]
    norm_num
    rw [abs_of_nonneg (by linarith), abs_of_neg htneg]
    ring
  · have htnonneg : 0 ≤ t := le_of_not_gt htneg
    have hround : round ((1 : ℝ) / 2 + t) = 1 := by
      rw [round_eq_iff]
      constructor <;> norm_num <;> linarith
    rw [UnitAddCircle.norm_eq, hround]
    norm_num
    rw [abs_of_nonpos (by linarith), abs_of_nonneg htnonneg]
    ring

/-- Along a coordinate path through an antipodal pair, the explicit Euclidean
torus radius has exactly the two-coordinate cusp profile. -/
theorem torusEuclideanDist_antipodal_first
    {t : ℝ} {x₂ y₂ : T1} (ht : |t| ≤ (1 : ℝ) / 2) :
    torusEuclideanDist (((-t : ℝ) : T1), x₂)
        ((((1 : ℝ) / 2 : ℝ) : T1), y₂) =
      Real.sqrt (((1 : ℝ) / 2 - |t|) ^ 2 + ‖x₂ - y₂‖ ^ 2) := by
  unfold torusEuclideanDist
  congr 2
  have hcoord :
      ‖(((-t : ℝ) : T1) - (((1 : ℝ) / 2 : ℝ) : T1))‖ =
        (1 : ℝ) / 2 - |t| := by
    rw [← norm_neg]
    simpa [sub_eq_add_neg, add_comm] using unitAddCircle_norm_half_add ht
  rw [hcoord]

/-- Product Haar measure on the unit two-torus. -/
noncomputable abbrev torusMeasure : Measure T2 :=
  (volume : Measure T1).prod (volume : Measure T1)

/-- Metric balls used in the root geometric-mixing condition. -/
def torusBall (x : T2) (r : ℝ) : Set T2 := Metric.ball x r

theorem torusBall_def (x : T2) (r : ℝ) :
    torusBall x r = Metric.ball x r := rfl

/-- The chosen Haar volume is probability-normalized. -/
theorem torusMeasure_univ : torusMeasure (Set.univ : Set T2) = 1 :=
  by
    simp [torusMeasure, Measure.prod_apply]

end Bressan
