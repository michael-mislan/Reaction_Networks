import proofs.DUnstableCores.RouthHurwitzDim3

/-!
# Rank-one contraction faces are cubically safe

At the projective boundary where one right-column scale tends to infinity,
an arrow/one-column edge contracts to a rank-one perturbation

`K = -diag(b) + v rᵀ`.

Writing `qᵢ = vᵢ rᵢ / bᵢ`, every principal coefficient of `-K` is a positive
diagonal factor times `1 - ∑ qᵢ` over the corresponding face.  The only
apparently new cubic Hurwitz coefficient is

`1 - (q₁+q₂+q₃) + q₁q₂ + q₁q₃ + q₂q₃`.

Among three real numbers two have the same sign.  For such a pair `(i,j)` and
the remaining index `k`, the coefficient is exactly

`(1-qᵢ-qⱼ)(1-qₖ) + qᵢqⱼ`.

Thus ordinary singleton and pair-face inequalities already make the
projective contraction face safe.  This removes the infinite-scale boundary
as a possible hidden door in the four-dimensional one-column edge program.
-/

namespace DUnstableCores

/-- The central cubic Hurwitz coefficient of a diagonal-minus-rank-one
contraction is nonnegative whenever every singleton and pair face has the
correct sign. -/
theorem rankOneContraction_cross_nonneg
    (q₁ q₂ q₃ : ℝ)
    (h₁ : q₁ ≤ 1) (h₂ : q₂ ≤ 1) (h₃ : q₃ ≤ 1)
    (h₁₂ : q₁ + q₂ ≤ 1) (h₁₃ : q₁ + q₃ ≤ 1)
    (h₂₃ : q₂ + q₃ ≤ 1) :
    0 ≤ 1 - (q₁ + q₂ + q₃) + q₁ * q₂ + q₁ * q₃ + q₂ * q₃ := by
  by_cases hq₁ : 0 ≤ q₁
  · by_cases hq₂ : 0 ≤ q₂
    · have hpair : 0 ≤ q₁ * q₂ := mul_nonneg hq₁ hq₂
      have hface : 0 ≤ 1 - q₁ - q₂ := by linarith
      have hsingle : 0 ≤ 1 - q₃ := by linarith
      have hprod : 0 ≤ (1 - q₁ - q₂) * (1 - q₃) :=
        mul_nonneg hface hsingle
      nlinarith
    · have hq₂' : q₂ ≤ 0 := le_of_not_ge hq₂
      by_cases hq₃ : 0 ≤ q₃
      · have hpair : 0 ≤ q₁ * q₃ := mul_nonneg hq₁ hq₃
        have hface : 0 ≤ 1 - q₁ - q₃ := by linarith
        have hsingle : 0 ≤ 1 - q₂ := by linarith
        have hprod : 0 ≤ (1 - q₁ - q₃) * (1 - q₂) :=
          mul_nonneg hface hsingle
        nlinarith
      · have hq₃' : q₃ ≤ 0 := le_of_not_ge hq₃
        have hpair : 0 ≤ q₂ * q₃ :=
          mul_nonneg_of_nonpos_of_nonpos hq₂' hq₃'
        have hface : 0 ≤ 1 - q₂ - q₃ := by linarith
        have hsingle : 0 ≤ 1 - q₁ := by linarith
        have hprod : 0 ≤ (1 - q₂ - q₃) * (1 - q₁) :=
          mul_nonneg hface hsingle
        nlinarith
  · have hq₁' : q₁ ≤ 0 := le_of_not_ge hq₁
    by_cases hq₂ : 0 ≤ q₂
    · by_cases hq₃ : 0 ≤ q₃
      · have hpair : 0 ≤ q₂ * q₃ := mul_nonneg hq₂ hq₃
        have hface : 0 ≤ 1 - q₂ - q₃ := by linarith
        have hsingle : 0 ≤ 1 - q₁ := by linarith
        have hprod : 0 ≤ (1 - q₂ - q₃) * (1 - q₁) :=
          mul_nonneg hface hsingle
        nlinarith
      · have hq₃' : q₃ ≤ 0 := le_of_not_ge hq₃
        have hpair : 0 ≤ q₁ * q₃ :=
          mul_nonneg_of_nonpos_of_nonpos hq₁' hq₃'
        have hface : 0 ≤ 1 - q₁ - q₃ := by linarith
        have hsingle : 0 ≤ 1 - q₂ := by linarith
        have hprod : 0 ≤ (1 - q₁ - q₃) * (1 - q₂) :=
          mul_nonneg hface hsingle
        nlinarith
    · have hq₂' : q₂ ≤ 0 := le_of_not_ge hq₂
      have hpair : 0 ≤ q₁ * q₂ :=
        mul_nonneg_of_nonpos_of_nonpos hq₁' hq₂'
      have hface : 0 ≤ 1 - q₁ - q₂ := by linarith
      have hsingle : 0 ≤ 1 - q₃ := by linarith
      have hprod : 0 ≤ (1 - q₁ - q₂) * (1 - q₃) :=
        mul_nonneg hface hsingle
      nlinarith

/-- Full cubic Routh--Hurwitz cross inequality for the rank-one contraction
coefficient profile.  The hypotheses are exactly nonnegative diagonal scales,
singleton faces, pair faces, and the full determinant face. -/
theorem rankOneContraction_cubicDelta2_nonneg
    (b₁ b₂ b₃ d₁ d₂ d₃ q₁ q₂ q₃ : ℝ)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (h₁ : q₁ ≤ 1) (h₂ : q₂ ≤ 1) (h₃ : q₃ ≤ 1)
    (h₁₂ : q₁ + q₂ ≤ 1) (h₁₃ : q₁ + q₃ ≤ 1)
    (h₂₃ : q₂ + q₃ ≤ 1) (h₁₂₃ : q₁ + q₂ + q₃ ≤ 1) :
    0 ≤
      (b₁ * (1 - q₁) * d₁ + b₂ * (1 - q₂) * d₂ +
          b₃ * (1 - q₃) * d₃) *
        (b₁ * b₂ * (1 - q₁ - q₂) * d₁ * d₂ +
          b₁ * b₃ * (1 - q₁ - q₃) * d₁ * d₃ +
          b₂ * b₃ * (1 - q₂ - q₃) * d₂ * d₃) -
        b₁ * b₂ * b₃ * (1 - q₁ - q₂ - q₃) * d₁ * d₂ * d₃ := by
  have hs₁ : 0 ≤ 1 - q₁ := by linarith
  have hs₂ : 0 ≤ 1 - q₂ := by linarith
  have hs₃ : 0 ≤ 1 - q₃ := by linarith
  have hs₁₂ : 0 ≤ 1 - q₁ - q₂ := by linarith
  have hs₁₃ : 0 ≤ 1 - q₁ - q₃ := by linarith
  have hs₂₃ : 0 ≤ 1 - q₂ - q₃ := by linarith
  have hs₁₂₃ : 0 ≤ 1 - q₁ - q₂ - q₃ := by linarith
  have hcross := rankOneContraction_cross_nonneg q₁ q₂ q₃
    h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
  have hterm₁ : 0 ≤
      b₁ ^ 2 * b₂ * (1 - q₁) * (1 - q₁ - q₂) * d₁ ^ 2 * d₂ := by
    positivity
  have hterm₂ : 0 ≤
      b₁ ^ 2 * b₃ * (1 - q₁) * (1 - q₁ - q₃) * d₁ ^ 2 * d₃ := by
    positivity
  have hterm₃ : 0 ≤
      b₁ * b₂ ^ 2 * (1 - q₂) * (1 - q₁ - q₂) * d₁ * d₂ ^ 2 := by
    positivity
  have hterm₄ : 0 ≤
      b₂ ^ 2 * b₃ * (1 - q₂) * (1 - q₂ - q₃) * d₂ ^ 2 * d₃ := by
    positivity
  have hterm₅ : 0 ≤
      b₁ * b₃ ^ 2 * (1 - q₃) * (1 - q₁ - q₃) * d₁ * d₃ ^ 2 := by
    positivity
  have hterm₆ : 0 ≤
      b₂ * b₃ ^ 2 * (1 - q₃) * (1 - q₂ - q₃) * d₂ * d₃ ^ 2 := by
    positivity
  have hcentral : 0 ≤
      b₁ * b₂ * b₃ *
        (2 * (1 - (q₁ + q₂ + q₃) + q₁ * q₂ + q₁ * q₃ + q₂ * q₃)) *
        d₁ * d₂ * d₃ := by
    have hb : 0 ≤ b₁ * b₂ * b₃ := by positivity
    have htwocross : 0 ≤ 2 *
        (1 - (q₁ + q₂ + q₃) + q₁ * q₂ + q₁ * q₃ + q₂ * q₃) := by
      positivity
    have hbcross : 0 ≤ b₁ * b₂ * b₃ *
        (2 * (1 - (q₁ + q₂ + q₃) + q₁ * q₂ + q₁ * q₃ + q₂ * q₃)) :=
      mul_nonneg hb htwocross
    have hbd₁ : 0 ≤ b₁ * b₂ * b₃ *
        (2 * (1 - (q₁ + q₂ + q₃) + q₁ * q₂ + q₁ * q₃ + q₂ * q₃)) * d₁ :=
      mul_nonneg hbcross hd₁
    have hbd₁d₂ : 0 ≤ b₁ * b₂ * b₃ *
        (2 * (1 - (q₁ + q₂ + q₃) + q₁ * q₂ + q₁ * q₃ + q₂ * q₃)) * d₁ * d₂ :=
      mul_nonneg hbd₁ hd₂
    exact mul_nonneg hbd₁d₂ hd₃
  have hsum : 0 ≤
      b₁ ^ 2 * b₂ * (1 - q₁) * (1 - q₁ - q₂) * d₁ ^ 2 * d₂ +
      b₁ ^ 2 * b₃ * (1 - q₁) * (1 - q₁ - q₃) * d₁ ^ 2 * d₃ +
      b₁ * b₂ ^ 2 * (1 - q₂) * (1 - q₁ - q₂) * d₁ * d₂ ^ 2 +
      b₂ ^ 2 * b₃ * (1 - q₂) * (1 - q₂ - q₃) * d₂ ^ 2 * d₃ +
      b₁ * b₃ ^ 2 * (1 - q₃) * (1 - q₁ - q₃) * d₁ * d₃ ^ 2 +
      b₂ * b₃ ^ 2 * (1 - q₃) * (1 - q₂ - q₃) * d₂ * d₃ ^ 2 +
      b₁ * b₂ * b₃ *
        (2 * (1 - (q₁ + q₂ + q₃) + q₁ * q₂ + q₁ * q₃ + q₂ * q₃)) *
        d₁ * d₂ * d₃ := by
    nlinarith [hterm₁, hterm₂, hterm₃, hterm₄, hterm₅, hterm₆, hcentral]
  calc
    (0 : ℝ) ≤
      b₁ ^ 2 * b₂ * (1 - q₁) * (1 - q₁ - q₂) * d₁ ^ 2 * d₂ +
      b₁ ^ 2 * b₃ * (1 - q₁) * (1 - q₁ - q₃) * d₁ ^ 2 * d₃ +
      b₁ * b₂ ^ 2 * (1 - q₂) * (1 - q₁ - q₂) * d₁ * d₂ ^ 2 +
      b₂ ^ 2 * b₃ * (1 - q₂) * (1 - q₂ - q₃) * d₂ ^ 2 * d₃ +
      b₁ * b₃ ^ 2 * (1 - q₃) * (1 - q₁ - q₃) * d₁ * d₃ ^ 2 +
      b₂ * b₃ ^ 2 * (1 - q₃) * (1 - q₂ - q₃) * d₂ * d₃ ^ 2 +
      b₁ * b₂ * b₃ *
        (2 * (1 - (q₁ + q₂ + q₃) + q₁ * q₂ + q₁ * q₃ + q₂ * q₃)) *
        d₁ * d₂ * d₃ := hsum
    _ =
      (b₁ * (1 - q₁) * d₁ + b₂ * (1 - q₂) * d₂ +
          b₃ * (1 - q₃) * d₃) *
        (b₁ * b₂ * (1 - q₁ - q₂) * d₁ * d₂ +
          b₁ * b₃ * (1 - q₁ - q₃) * d₁ * d₃ +
          b₂ * b₃ * (1 - q₂ - q₃) * d₂ * d₃) -
        b₁ * b₂ * b₃ * (1 - q₁ - q₂ - q₃) * d₁ * d₂ * d₃ := by
      ring

end DUnstableCores
