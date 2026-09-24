import Mathlib

/-! Scalar interface calculus for interacting autocatalytic cores.

After eliminating a triangular private sector with gain `m`, shared-current
compatibility is the requirement that its normalized interface response lies
in the open interval `(R / m, R)`, where `R` is the sum of reciprocal private
barriers.  This file proves the exact two-core composition rule. -/

namespace ThermoCoreCompatibility.InterfaceProfile

/-- Two open real intervals have a common point. -/
def OpenIntervalsIntersect (a b c d : ℝ) : Prop :=
  ∃ q, a < q ∧ q < b ∧ c < q ∧ q < d

theorem openIntervalsIntersect_iff {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) :
    OpenIntervalsIntersect a b c d ↔ a < d ∧ c < b := by
  constructor
  · rintro ⟨q, haq, hqb, hcq, hqd⟩
    exact ⟨lt_trans haq hqd, lt_trans hcq hqb⟩
  · rintro ⟨had, hcb⟩
    have hmm : max a c < min b d := by
      apply (max_lt_iff).2
      exact ⟨(lt_min_iff).2 ⟨hab, had⟩, (lt_min_iff).2 ⟨hcb, hcd⟩⟩
    refine ⟨(max a c + min b d) / 2, ?_, ?_, ?_, ?_⟩
    · have := le_max_left a c
      linarith
    · have := min_le_left b d
      linarith
    · have := le_max_right a c
      linarith
    · have := min_le_right b d
      linarith

/-- The exact scalar response interval of a gain-`m` core with private
response coefficient `R`. -/
def Admissible (m R q : ℝ) : Prop := R / m < q ∧ q < R

theorem admissible_nonempty {m R : ℝ} (hm : 1 < m) (hR : 0 < R) :
    R / m < R := by
  have hm0 : 0 < m := by linarith
  apply (div_lt_iff₀ hm0).2
  nlinarith

/-- Productive current ratios for a two-edge private path ending in gain `m`. -/
def TriangleCone (m u v : ℝ) : Prop := 1 / m < v ∧ v < u ∧ u < 1

/-- Image of the productive cone under a positive weighted activity-drop map. -/
def WeightedTriangleResponse (m x y q : ℝ) : Prop :=
  ∃ u v, TriangleCone m u v ∧ q = x * u + y * v

/-- A positive weighted two-edge triangle has exactly the open response
interval `((x+y)/m, x+y)`. -/
theorem weightedTriangleResponse_iff {m x y q : ℝ}
    (hm : 1 < m) (hx : 0 < x) (hy : 0 < y) :
    WeightedTriangleResponse m x y q ↔ (x + y) / m < q ∧ q < x + y := by
  have hm0 : 0 < m := by linarith
  constructor
  · rintro ⟨u, v, ⟨hlv, hvu, hu1⟩, rfl⟩
    have hlu : 1 / m < u := lt_trans hlv hvu
    have hv1 : v < 1 := lt_trans hvu hu1
    constructor
    · have hxu := mul_lt_mul_of_pos_left hlu hx
      have hyv := mul_lt_mul_of_pos_left hlv hy
      have hsplit : (x + y) / m = x * (1 / m) + y * (1 / m) := by ring
      rw [hsplit]
      linarith
    · have hxu := mul_lt_mul_of_pos_left hu1 hx
      have hyv := mul_lt_mul_of_pos_left hv1 hy
      nlinarith
  · rintro ⟨hlo, hhi⟩
    let S : ℝ := x + y
    let l : ℝ := 1 / m
    let t : ℝ := q / S
    let e : ℝ := (t - l) * (1 - t) / (2 * S)
    have hS : 0 < S := by dsimp [S]; linarith
    have htlo : l < t := by
      dsimp [l, t, S]
      rw [div_lt_div_iff₀ hm0 hS]
      simpa [one_mul, mul_comm] using (div_lt_iff₀ hm0).1 hlo
    have hthi : t < 1 := by
      dsimp [t, S]
      exact (div_lt_one hS).2 hhi
    have hl0 : 0 < l := by dsimp [l]; positivity
    have ht0 : 0 < t := lt_trans hl0 htlo
    have he : 0 < e := by dsimp [e]; positivity
    have hsmallx : e * x < t - l := by
      have haux : (1 - t) * x < 2 * S := by
        have h1t : 1 - t < 1 := by linarith
        have hprod : (1 - t) * x < x := by
          simpa using mul_lt_mul_of_pos_right h1t hx
        dsimp [S]
        nlinarith
      dsimp [e]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (show 0 < 2 * S by positivity)]
      have := mul_lt_mul_of_pos_left haux (show 0 < t - l by linarith)
      nlinarith
    have hsmally : e * y < 1 - t := by
      have haux : (t - l) * y < 2 * S := by
        have htl : t - l < 1 := by linarith
        have hprod : (t - l) * y < y := by
          simpa using mul_lt_mul_of_pos_right htl hy
        dsimp [S]
        nlinarith
      dsimp [e]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (show 0 < 2 * S by positivity)]
      have := mul_lt_mul_of_pos_right haux (show 0 < 1 - t by linarith)
      nlinarith
    refine ⟨t + e * y, t - e * x, ?_, ?_⟩
    · exact ⟨by linarith, by nlinarith [mul_pos he hS], by linarith⟩
    · have hqt : q = S * t := by
        dsimp [t]
        field_simp
      rw [hqt]
      dsimp [S]
      ring

/-- Literal barrier parameterization of the triangle response. -/
def BarrierTriangleResponse (m b₀ b₁ b₂ q : ℝ) : Prop :=
  WeightedTriangleResponse m (b₀ / b₁) (b₀ / b₂) q

/-- Literal current-level interface equations for the triangle

`A → B → C → m A`.

Here `j₀,j₁,j₂` are the three oriented reaction currents.  The three strict
inequalities are exactly positive net production of `A,C,B`, respectively,
and the last equality is the barrier-weighted interface equation before
normalization by the shared current `j₀`. -/
def LiteralTriangleCurrents
    (m b₀ b₁ b₂ q j₀ j₁ j₂ : ℝ) : Prop :=
  0 < j₀ ∧
    0 < m * j₂ - j₀ ∧
    0 < j₁ - j₂ ∧
    0 < j₀ - j₁ ∧
    q = b₀ * (j₁ / (b₁ * j₀) + j₂ / (b₂ * j₀))

/-- The uneliminated source-level interface predicate. -/
def LiteralBarrierTriangleResponse (m b₀ b₁ b₂ q : ℝ) : Prop :=
  ∃ j₀ j₁ j₂, LiteralTriangleCurrents m b₀ b₁ b₂ q j₀ j₁ j₂

/-- Exact source adapter: normalizing literal productive currents by their
positive shared current gives precisely the abstract barrier response. -/
theorem literalBarrierTriangleResponse_iff_barrierTriangleResponse
    {m b₀ b₁ b₂ q : ℝ}
    (hm : 1 < m) :
    LiteralBarrierTriangleResponse m b₀ b₁ b₂ q ↔
      BarrierTriangleResponse m b₀ b₁ b₂ q := by
  have hm0 : 0 < m := by linarith
  constructor
  · rintro ⟨j₀, j₁, j₂, hj₀, hA, hC, hB, hq⟩
    refine ⟨j₁ / j₀, j₂ / j₀, ?_, ?_⟩
    · constructor
      · rw [div_lt_div_iff₀ hm0 hj₀]
        nlinarith
      constructor
      · rw [div_lt_div_iff₀ hj₀ hj₀]
        nlinarith [mul_pos (show 0 < j₁ - j₂ by linarith) hj₀]
      · exact (div_lt_one hj₀).2 (by linarith)
    · rw [hq]
      ring
  · rintro ⟨u, v, ⟨hv, hvu, hu⟩, hq⟩
    refine ⟨1, u, v, by norm_num, ?_, by linarith, by linarith, ?_⟩
    · have hmv : 1 < v * m := (div_lt_iff₀ hm0).1 hv
      nlinarith
    · rw [hq]
      ring

theorem barrierTriangleResponse_iff {m b₀ b₁ b₂ q : ℝ}
    (hm : 1 < m) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    BarrierTriangleResponse m b₀ b₁ b₂ q ↔
      b₀ * (1 / b₁ + 1 / b₂) / m < q ∧
        q < b₀ * (1 / b₁ + 1 / b₂) := by
  have hx : 0 < b₀ / b₁ := div_pos hb₀ hb₁
  have hy : 0 < b₀ / b₂ := div_pos hb₀ hb₂
  have hsum : b₀ / b₁ + b₀ / b₂ = b₀ * (1 / b₁ + 1 / b₂) := by
    ring
  simpa only [BarrierTriangleResponse, hsum] using
    (weightedTriangleResponse_iff (m := m) (x := b₀ / b₁)
      (y := b₀ / b₂) (q := q) hm hx hy)

/-- The scalar interval in the interface calculus is therefore not an
independent abstraction: it is the exact projection of the literal
barrier-weighted productive-current equations. -/
theorem literalBarrierTriangleResponse_iff_interval {m b₀ b₁ b₂ q : ℝ}
    (hm : 1 < m) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    LiteralBarrierTriangleResponse m b₀ b₁ b₂ q ↔
      b₀ * (1 / b₁ + 1 / b₂) / m < q ∧
        q < b₀ * (1 / b₁ + 1 / b₂) := by
  exact (literalBarrierTriangleResponse_iff_barrierTriangleResponse
    hm).trans (barrierTriangleResponse_iff hm hb₀ hb₁ hb₂)

/-- Exact composition law for two reduced cores.  Their response intervals
overlap precisely when the response ratio lies between the reciprocal left
gain and the right gain. -/
theorem commonResponse_iff_ratio {mL mR RL RR : ℝ}
    (hmL : 1 < mL) (hmR : 1 < mR) (hRL : 0 < RL) (hRR : 0 < RR) :
    (∃ q, Admissible mL RL q ∧ Admissible mR RR q) ↔
      1 / mL < RR / RL ∧ RR / RL < mR := by
  have hmL0 : 0 < mL := by linarith
  have hmR0 : 0 < mR := by linarith
  have hLint : RL / mL < RL := admissible_nonempty hmL hRL
  have hRint : RR / mR < RR := admissible_nonempty hmR hRR
  rw [show (∃ q, Admissible mL RL q ∧ Admissible mR RR q) =
      OpenIntervalsIntersect (RL / mL) RL (RR / mR) RR by
        apply propext
        simp only [Admissible, OpenIntervalsIntersect]
        aesop]
  rw [openIntervalsIntersect_iff hLint hRint]
  constructor
  · rintro ⟨hLR, hRLcross⟩
    constructor
    · apply (div_lt_div_iff₀ hmL0 hRL).2
      rw [one_mul]
      exact (div_lt_iff₀ hmL0).1 hLR
    · rw [div_lt_iff₀ hRL]
      simpa [mul_comm] using (div_lt_iff₀ hmR0).1 hRLcross
  · rintro ⟨hratioL, hratioR⟩
    constructor
    · rw [div_lt_iff₀ hmL0]
      simpa using (div_lt_div_iff₀ hmL0 hRL).1 hratioL
    · rw [div_lt_iff₀ hmR0]
      simpa [mul_comm] using (div_lt_iff₀ hRL).1 hratioR

end ThermoCoreCompatibility.InterfaceProfile
