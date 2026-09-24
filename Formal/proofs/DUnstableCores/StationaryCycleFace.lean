import proofs.DUnstableCores.RankOneContraction

/-!
# A finite quartic stationary circuit must expose a cycle face

The minimized scalar quartic obstruction attempts to place a new column over
a safe negative three-cycle while making every three-species face singular.
After normalizing the three pair minors by the cycle diagonal losses, let
`s₁,s₂,s₃` be their nonnegative deficits.  Their small weighted sum gives
`s₁+s₂+s₃ < 1`.

The vanishing triple faces and rank-one coupling identities force two reverse
cycle products to be at most `-1` and the closing product to be at least the
cycle gain `g`.  Thus the full determinant response is at least `3g`.  But the
prescribed zero full determinant makes it `g + p(1-∑sᵢ) ≤ g+p`, where `p` is
the diagonal product.  A subcritical cycle in the regime `p < 2g` cannot meet
both requirements.

This is the exact algebraic core of the Z3 UNSAT face-localization experiment;
the theorem is stated at the normalized determinant interface so it can be
docked to a later general one-column coefficient adapter.
-/

namespace DUnstableCores

/-- The normalized reverse-cycle identities and the full determinant equation
are incompatible when the closing cycle gain exceeds half the diagonal
product. -/
theorem stationaryCycleFace_impossible
    (g p s₁ s₂ s₃ u v w : ℝ)
    (hg : 0 < g) (hp : 0 ≤ p) (hgain : p < 2 * g)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₃ : 0 ≤ s₃)
    (hsum : s₁ + s₂ + s₃ < 1)
    (huEq : u * (-(1 - s₁ - s₂)) = (1 - s₁) * (1 - s₂))
    (hvEq : v * (-(1 - s₂ - s₃)) = (1 - s₂) * (1 - s₃))
    (hwEq : w * (1 - s₁ - s₃) = g * (1 - s₁) * (1 - s₃))
    (hfull : w - g * (u + v) = g + p * (1 - (s₁ + s₂ + s₃))) :
    False := by
  have hd₁₂ : 0 < 1 - s₁ - s₂ := by nlinarith
  have hd₂₃ : 0 < 1 - s₂ - s₃ := by nlinarith
  have hd₁₃ : 0 < 1 - s₁ - s₃ := by nlinarith
  have hnum₁₂ :
      (1 - s₁) * (1 - s₂) = (1 - s₁ - s₂) + s₁ * s₂ := by ring
  have hnum₂₃ :
      (1 - s₂) * (1 - s₃) = (1 - s₂ - s₃) + s₂ * s₃ := by ring
  have hnum₁₃ :
      (1 - s₁) * (1 - s₃) = (1 - s₁ - s₃) + s₁ * s₃ := by ring
  have hle₁₂ : 1 - s₁ - s₂ ≤ (1 - s₁) * (1 - s₂) := by
    rw [hnum₁₂]
    exact le_add_of_nonneg_right (mul_nonneg hs₁ hs₂)
  have hle₂₃ : 1 - s₂ - s₃ ≤ (1 - s₂) * (1 - s₃) := by
    rw [hnum₂₃]
    exact le_add_of_nonneg_right (mul_nonneg hs₂ hs₃)
  have hle₁₃ : 1 - s₁ - s₃ ≤ (1 - s₁) * (1 - s₃) := by
    rw [hnum₁₃]
    exact le_add_of_nonneg_right (mul_nonneg hs₁ hs₃)
  have huRewrite : (-u) * (1 - s₁ - s₂) = (1 - s₁) * (1 - s₂) := by
    calc
      (-u) * (1 - s₁ - s₂) = u * (-(1 - s₁ - s₂)) := by ring
      _ = (1 - s₁) * (1 - s₂) := huEq
  have hvRewrite : (-v) * (1 - s₂ - s₃) = (1 - s₂) * (1 - s₃) := by
    calc
      (-v) * (1 - s₂ - s₃) = v * (-(1 - s₂ - s₃)) := by ring
      _ = (1 - s₂) * (1 - s₃) := hvEq
  have huBound : 1 ≤ -u := by
    have hmul : 1 * (1 - s₁ - s₂) ≤ (-u) * (1 - s₁ - s₂) := by
      calc
        1 * (1 - s₁ - s₂) = 1 - s₁ - s₂ := by ring
        _ ≤ (1 - s₁) * (1 - s₂) := hle₁₂
        _ = (-u) * (1 - s₁ - s₂) := huRewrite.symm
    exact le_of_mul_le_mul_right hmul hd₁₂
  have hvBound : 1 ≤ -v := by
    have hmul : 1 * (1 - s₂ - s₃) ≤ (-v) * (1 - s₂ - s₃) := by
      calc
        1 * (1 - s₂ - s₃) = 1 - s₂ - s₃ := by ring
        _ ≤ (1 - s₂) * (1 - s₃) := hle₂₃
        _ = (-v) * (1 - s₂ - s₃) := hvRewrite.symm
    exact le_of_mul_le_mul_right hmul hd₂₃
  have hwBound : g ≤ w := by
    have hmul : g * (1 - s₁ - s₃) ≤ w * (1 - s₁ - s₃) := by
      calc
        g * (1 - s₁ - s₃) ≤ g * ((1 - s₁) * (1 - s₃)) :=
          mul_le_mul_of_nonneg_left hle₁₃ hg.le
        _ = g * (1 - s₁) * (1 - s₃) := by ring
        _ = w * (1 - s₁ - s₃) := hwEq.symm
    exact le_of_mul_le_mul_right hmul hd₁₃
  have hgu : g ≤ -(g * u) := by
    have hum : u ≤ -1 := by linarith
    have := mul_le_mul_of_nonneg_left hum hg.le
    linarith
  have hgv : g ≤ -(g * v) := by
    have hvm : v ≤ -1 := by linarith
    have := mul_le_mul_of_nonneg_left hvm hg.le
    linarith
  have hleft : 3 * g ≤ w - g * (u + v) := by
    nlinarith [hwBound, hgu, hgv]
  have hS : 0 ≤ s₁ + s₂ + s₃ := by positivity
  have hfactor : 1 - (s₁ + s₂ + s₃) ≤ 1 := by linarith
  have hright : g + p * (1 - (s₁ + s₂ + s₃)) ≤ g + p := by
    have := mul_le_mul_of_nonneg_left hfactor hp
    linarith
  nlinarith [hleft, hright, hfull, hgain]

/-- Adding the multiplicative circuit-consistency identity removes the gain
restriction entirely.  After eliminating the gain and diagonal product, the
remaining equation is the square of
`1 - (s₁+s₂+s₃) + s₁*s₂ + s₁*s₃ + s₂*s₃`, which is strictly positive. -/
theorem stationaryCycleFace_product_impossible
    (g p s₁ s₂ s₃ u v w : ℝ)
    (hg : 0 < g)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₃ : 0 ≤ s₃)
    (hsum : s₁ + s₂ + s₃ < 1)
    (huEq : u * (-(1 - s₁ - s₂)) = (1 - s₁) * (1 - s₂))
    (hvEq : v * (-(1 - s₂ - s₃)) = (1 - s₂) * (1 - s₃))
    (hwEq : w * (1 - s₁ - s₃) = g * (1 - s₁) * (1 - s₃))
    (hprod :
      u * v * w = p * ((1 - s₁) * (1 - s₂) * (1 - s₃)))
    (hfull : w - g * (u + v) = g + p * (1 - (s₁ + s₂ + s₃))) :
    False := by
  let d₁₂ := 1 - s₁ - s₂
  let d₂₃ := 1 - s₂ - s₃
  let d₁₃ := 1 - s₁ - s₃
  let n₁₂ := (1 - s₁) * (1 - s₂)
  let n₂₃ := (1 - s₂) * (1 - s₃)
  let n₁₃ := (1 - s₁) * (1 - s₃)
  let N := (1 - s₁) * (1 - s₂) * (1 - s₃)
  have hd₁ : 0 < 1 - s₁ := by nlinarith
  have hd₂ : 0 < 1 - s₂ := by nlinarith
  have hd₃ : 0 < 1 - s₃ := by nlinarith
  have hNpos : 0 < N := by
    dsimp only [N]
    positivity
  have huNeg : (-u) * d₁₂ = n₁₂ := by
    dsimp only [d₁₂, n₁₂]
    calc
      (-u) * (1 - s₁ - s₂) = u * (-(1 - s₁ - s₂)) := by ring
      _ = (1 - s₁) * (1 - s₂) := huEq
  have hvNeg : (-v) * d₂₃ = n₂₃ := by
    dsimp only [d₂₃, n₂₃]
    calc
      (-v) * (1 - s₂ - s₃) = v * (-(1 - s₂ - s₃)) := by ring
      _ = (1 - s₂) * (1 - s₃) := hvEq
  have hwPos : w * d₁₃ = g * n₁₃ := by
    dsimp only [d₁₃, n₁₃]
    calc
      w * (1 - s₁ - s₃) = g * (1 - s₁) * (1 - s₃) := hwEq
      _ = g * ((1 - s₁) * (1 - s₃)) := by ring
  have hlocalProd :
      (u * v * w) * (d₁₂ * d₂₃ * d₁₃) = g * (N * N) := by
    calc
      (u * v * w) * (d₁₂ * d₂₃ * d₁₃) =
          ((-u) * d₁₂) * ((-v) * d₂₃) * (w * d₁₃) := by ring
      _ = n₁₂ * n₂₃ * (g * n₁₃) := by rw [huNeg, hvNeg, hwPos]
      _ = g * (N * N) := by
        dsimp only [n₁₂, n₂₃, n₁₃, N]
        ring
  have hPDMult :
      N * (p * (d₁₂ * d₂₃ * d₁₃)) = N * (g * N) := by
    calc
      N * (p * (d₁₂ * d₂₃ * d₁₃)) =
          (p * N) * (d₁₂ * d₂₃ * d₁₃) := by ring
      _ = (u * v * w) * (d₁₂ * d₂₃ * d₁₃) := by rw [hprod]
      _ = g * (N * N) := hlocalProd
      _ = N * (g * N) := by ring
  have hPD : p * (d₁₂ * d₂₃ * d₁₃) = g * N :=
    mul_left_cancel₀ hNpos.ne' hPDMult
  have hscaled :
      g * (n₁₃ * d₁₂ * d₂₃ + n₁₂ * d₂₃ * d₁₃ + n₂₃ * d₁₂ * d₁₃) =
        g * (d₁₂ * d₂₃ * d₁₃ + N * (1 - (s₁ + s₂ + s₃))) := by
    calc
      g * (n₁₃ * d₁₂ * d₂₃ + n₁₂ * d₂₃ * d₁₃ + n₂₃ * d₁₂ * d₁₃) =
          (w * d₁₃) * d₁₂ * d₂₃
            + g * ((-u) * d₁₂) * d₂₃ * d₁₃
            + g * ((-v) * d₂₃) * d₁₂ * d₁₃ := by
              rw [huNeg, hvNeg, hwPos]
              ring
      _ = (w - g * (u + v)) * (d₁₂ * d₂₃ * d₁₃) := by ring
      _ = (g + p * (1 - (s₁ + s₂ + s₃))) *
            (d₁₂ * d₂₃ * d₁₃) := by rw [hfull]
      _ = g * (d₁₂ * d₂₃ * d₁₃ + N * (1 - (s₁ + s₂ + s₃))) := by
            linear_combination (1 - (s₁ + s₂ + s₃)) * hPD
  have hpoly :
      n₁₃ * d₁₂ * d₂₃ + n₁₂ * d₂₃ * d₁₃ + n₂₃ * d₁₂ * d₁₃ =
        d₁₂ * d₂₃ * d₁₃ + N * (1 - (s₁ + s₂ + s₃)) :=
    mul_left_cancel₀ hg.ne' hscaled
  have hsquare :
      (1 - (s₁ + s₂ + s₃) + s₁ * s₂ + s₁ * s₃ + s₂ * s₃) ^ 2 = 0 := by
    have hid :
        n₁₃ * d₁₂ * d₂₃ + n₁₂ * d₂₃ * d₁₃ + n₂₃ * d₁₂ * d₁₃
            - (d₁₂ * d₂₃ * d₁₃ + N * (1 - (s₁ + s₂ + s₃))) =
          (1 - (s₁ + s₂ + s₃) + s₁ * s₂ + s₁ * s₃ + s₂ * s₃) ^ 2 := by
      dsimp only [d₁₂, d₂₃, d₁₃, n₁₂, n₂₃, n₁₃, N]
      ring
    rw [← hid]
    exact sub_eq_zero.mpr hpoly
  have hbase :
      0 < 1 - (s₁ + s₂ + s₃) + s₁ * s₂ + s₁ * s₃ + s₂ * s₃ := by
    have hgap : 0 < 1 - (s₁ + s₂ + s₃) := sub_pos.mpr hsum
    have hpairs : 0 ≤ s₁ * s₂ + s₁ * s₃ + s₂ * s₃ := by positivity
    have hrepr :
        1 - (s₁ + s₂ + s₃) + s₁ * s₂ + s₁ * s₃ + s₂ * s₃ =
          (1 - (s₁ + s₂ + s₃)) + (s₁ * s₂ + s₁ * s₃ + s₂ * s₃) := by
      ring
    rw [hrepr]
    exact add_pos_of_pos_of_nonneg hgap hpairs
  exact (ne_of_gt hbase) ((sq_eq_zero_iff).mp hsquare)

/-- Exact factorization of the nonzero triple-face-slack residual.  The three
linear factors are the local compatibility margins; the final monomial is the
alternating cycle closure. -/
theorem stationaryFaceSlack_factorization
    (s₁ s₂ s₃ t₁₂ t₂₃ t₁₃ : ℝ) :
    let q := 1 - (s₁ + s₂ + s₃) + s₁ * s₂ + s₁ * s₃ + s₂ * s₃
    let N := (1 - s₁) * (1 - s₂) * (1 - s₃)
    let F := q ^ 2
      - q * (s₃ * t₁₂ + s₁ * t₂₃ + s₂ * t₁₃)
      + s₁ * s₃ * t₁₂ * t₂₃
      + s₂ * s₃ * t₁₂ * t₁₃
      + s₁ * s₂ * t₂₃ * t₁₃
      - t₁₂ * t₂₃ * t₁₃
    q * F =
      (q - s₃ * t₁₂) * (q - s₁ * t₂₃) * (q - s₂ * t₁₃)
        - N * t₁₂ * t₂₃ * t₁₃ := by
  dsimp only
  ring

/-- If the two slacks incident to the middle sign class do not expose an
exchange, the face-slack residual can vanish only on the complementary local
compatibility margin.  Cyclic relabelings give the other two versions. -/
theorem stationaryFaceSlack_exchange_or_margin13_zero
    (q s₁ s₂ s₃ t₁₂ t₂₃ t₁₃ : ℝ)
    (hq : 0 < q) (ht₁₂ : 0 ≤ t₁₂) (ht₂₃ : 0 ≤ t₂₃)
    (hF : q ^ 2
      - q * (s₃ * t₁₂ + s₁ * t₂₃ + s₂ * t₁₃)
      + s₁ * s₃ * t₁₂ * t₂₃
      + s₂ * s₃ * t₁₂ * t₁₃
      + s₁ * s₂ * t₂₃ * t₁₃
      - t₁₂ * t₂₃ * t₁₃ = 0) :
    0 < t₁₂ ∨ 0 < t₂₃ ∨ q - s₂ * t₁₃ = 0 := by
  rcases eq_or_lt_of_le ht₁₂ with rfl | ht₁₂pos
  · rcases eq_or_lt_of_le ht₂₃ with rfl | ht₂₃pos
    · right
      right
      have hmul : q * (q - s₂ * t₁₃) = 0 := by
        linear_combination hF
      exact (mul_eq_zero.mp hmul).resolve_left hq.ne'
    · exact Or.inr (Or.inl ht₂₃pos)
  · exact Or.inl ht₁₂pos

/-- Cyclic companion: if the slacks incident to the first sign class do not
expose an exchange, the complementary margin vanishes. -/
theorem stationaryFaceSlack_exchange_or_margin23_zero
    (q s₁ s₂ s₃ t₁₂ t₂₃ t₁₃ : ℝ)
    (hq : 0 < q) (ht₁₂ : 0 ≤ t₁₂) (ht₁₃ : 0 ≤ t₁₃)
    (hF : q ^ 2
      - q * (s₃ * t₁₂ + s₁ * t₂₃ + s₂ * t₁₃)
      + s₁ * s₃ * t₁₂ * t₂₃
      + s₂ * s₃ * t₁₂ * t₁₃
      + s₁ * s₂ * t₂₃ * t₁₃
      - t₁₂ * t₂₃ * t₁₃ = 0) :
    0 < t₁₂ ∨ 0 < t₁₃ ∨ q - s₁ * t₂₃ = 0 := by
  rcases eq_or_lt_of_le ht₁₂ with rfl | ht₁₂pos
  · rcases eq_or_lt_of_le ht₁₃ with rfl | ht₁₃pos
    · right
      right
      have hmul : q * (q - s₁ * t₂₃) = 0 := by
        linear_combination hF
      exact (mul_eq_zero.mp hmul).resolve_left hq.ne'
    · exact Or.inr (Or.inl ht₁₃pos)
  · exact Or.inl ht₁₂pos

/-- Pair positivity and one negative cross-product force one of the two
incident coupling pairs to consist of two negative entries.  In a literal
source child this is precisely the reactant eligibility needed for the odd
column transposition. -/
theorem alternatingCoupling_negative_pair
    (r₀ r₁ c₀ c₁ : ℝ)
    (hpair₀ : 0 < r₀ * c₀) (hpair₁ : 0 < r₁ * c₁)
    (hcross : r₁ * c₀ < 0) :
    (r₀ < 0 ∧ c₀ < 0) ∨ (r₁ < 0 ∧ c₁ < 0) := by
  rcases (mul_pos_iff.mp hpair₀) with hpositive | hnegative
  · right
    have hr₁ : r₁ < 0 := by
      rcases (mul_neg_iff.mp hcross) with h | h
      · exact (not_lt_of_ge hpositive.2.le h.2).elim
      · exact h.1
    have hc₁ : c₁ < 0 := by
      rcases (mul_pos_iff.mp hpair₁) with h | h
      · exact (not_lt_of_ge h.1.le hr₁).elim
      · exact h.2
    exact ⟨hr₁, hc₁⟩
  · exact Or.inl hnegative

/-- Matrix-shaped adapter for an arrow extension of a negative three-cycle.

The `pair` equations normalize the three two-species principal minors, the
`triple` equations are the three vanishing three-species principal minors,
and `hdet` is the expanded four-by-four determinant.  Thus this theorem docks
the abstract holonomy variables to literal row/column coupling products. -/
theorem stationaryArrowCycleFace_impossible
    (b₁ b₂ b₃ g s₁ s₂ s₃ r₀ r₁ r₂ c₀ c₁ c₂ : ℝ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃) (hg : 0 < g)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₃ : 0 ≤ s₃)
    (hsum : s₁ + s₂ + s₃ < 1)
    (hpair₁ : r₀ * c₀ = b₁ * (1 - s₁))
    (hpair₂ : r₁ * c₁ = b₂ * (1 - s₂))
    (hpair₃ : r₂ * c₂ = b₃ * (1 - s₃))
    (htriple₁₂ : r₁ * c₀ = -(b₁ * b₂ * (1 - s₁ - s₂)))
    (htriple₂₃ : r₂ * c₁ = -(b₂ * b₃ * (1 - s₂ - s₃)))
    (htriple₁₃ : g * r₀ * c₂ = b₁ * b₃ * (1 - s₁ - s₃))
    (hdet :
      b₁ * b₂ * b₃
        - b₁ * b₂ * c₂ * r₂
        - b₁ * b₃ * c₁ * r₁
        - b₁ * c₁ * r₂
        - b₂ * b₃ * c₀ * r₀
        + b₂ * c₂ * g * r₀
        - b₃ * c₀ * r₁
        - c₀ * r₂
        + c₁ * g * r₀
        + c₂ * g * r₁
        + g = 0) :
    False := by
  let p := b₁ * b₂ * b₃
  let u := r₀ * c₁
  let v := r₁ * c₂
  let w := r₂ * c₀
  have huMult :
      (b₁ * b₂) * (u * (-(1 - s₁ - s₂))) =
        (b₁ * b₂) * ((1 - s₁) * (1 - s₂)) := by
    calc
      (b₁ * b₂) * (u * (-(1 - s₁ - s₂))) =
          (r₀ * c₁) * (-(b₁ * b₂ * (1 - s₁ - s₂))) := by
            simp only [u]
            ring
      _ = (r₀ * c₁) * (r₁ * c₀) := by rw [htriple₁₂]
      _ = (r₀ * c₀) * (r₁ * c₁) := by ring
      _ = (b₁ * (1 - s₁)) * (b₂ * (1 - s₂)) := by
            rw [hpair₁, hpair₂]
      _ = (b₁ * b₂) * ((1 - s₁) * (1 - s₂)) := by ring
  have huEq : u * (-(1 - s₁ - s₂)) = (1 - s₁) * (1 - s₂) :=
    mul_left_cancel₀ (mul_ne_zero hb₁.ne' hb₂.ne') huMult
  have hvMult :
      (b₂ * b₃) * (v * (-(1 - s₂ - s₃))) =
        (b₂ * b₃) * ((1 - s₂) * (1 - s₃)) := by
    calc
      (b₂ * b₃) * (v * (-(1 - s₂ - s₃))) =
          (r₁ * c₂) * (-(b₂ * b₃ * (1 - s₂ - s₃))) := by
            simp only [v]
            ring
      _ = (r₁ * c₂) * (r₂ * c₁) := by rw [htriple₂₃]
      _ = (r₁ * c₁) * (r₂ * c₂) := by ring
      _ = (b₂ * (1 - s₂)) * (b₃ * (1 - s₃)) := by
            rw [hpair₂, hpair₃]
      _ = (b₂ * b₃) * ((1 - s₂) * (1 - s₃)) := by ring
  have hvEq : v * (-(1 - s₂ - s₃)) = (1 - s₂) * (1 - s₃) :=
    mul_left_cancel₀ (mul_ne_zero hb₂.ne' hb₃.ne') hvMult
  have hwMult :
      (b₁ * b₃) * (w * (1 - s₁ - s₃)) =
        (b₁ * b₃) * (g * (1 - s₁) * (1 - s₃)) := by
    calc
      (b₁ * b₃) * (w * (1 - s₁ - s₃)) =
          (r₂ * c₀) * (b₁ * b₃ * (1 - s₁ - s₃)) := by
            simp only [w]
            ring
      _ = (r₂ * c₀) * (g * r₀ * c₂) := by rw [htriple₁₃]
      _ = g * (r₀ * c₀) * (r₂ * c₂) := by ring
      _ = g * (b₁ * (1 - s₁)) * (b₃ * (1 - s₃)) := by
            rw [hpair₁, hpair₃]
      _ = (b₁ * b₃) * (g * (1 - s₁) * (1 - s₃)) := by ring
  have hwEq : w * (1 - s₁ - s₃) = g * (1 - s₁) * (1 - s₃) :=
    mul_left_cancel₀ (mul_ne_zero hb₁.ne' hb₃.ne') hwMult
  have hdetRewrite :
      p * (1 - (s₁ + s₂ + s₃)) - w + g * u + g * v + g = 0 := by
    have hshape :
        b₁ * b₂ * b₃
            - b₁ * b₂ * c₂ * r₂
            - b₁ * b₃ * c₁ * r₁
            - b₁ * c₁ * r₂
            - b₂ * b₃ * c₀ * r₀
            + b₂ * c₂ * g * r₀
            - b₃ * c₀ * r₁
            - c₀ * r₂
            + c₁ * g * r₀
            + c₂ * g * r₁
            + g =
          p * (1 - (s₁ + s₂ + s₃)) - w + g * u + g * v + g := by
      calc
        _ = b₁ * b₂ * b₃
              - (b₁ * b₂ * b₃) * (1 - s₃)
              - (b₁ * b₂ * b₃) * (1 - s₂)
              - b₁ * (r₂ * c₁)
              - (b₁ * b₂ * b₃) * (1 - s₁)
              + b₂ * (g * r₀ * c₂)
              - b₃ * (r₁ * c₀)
              - w + g * u + g * v + g := by
                dsimp only [u, v, w]
                linear_combination
                  -(b₁ * b₂) * hpair₃
                    - (b₁ * b₃) * hpair₂
                    - (b₂ * b₃) * hpair₁
        _ = b₁ * b₂ * b₃
              - (b₁ * b₂ * b₃) * (1 - s₃)
              - (b₁ * b₂ * b₃) * (1 - s₂)
              - b₁ * (-(b₂ * b₃ * (1 - s₂ - s₃)))
              - (b₁ * b₂ * b₃) * (1 - s₁)
              + b₂ * (b₁ * b₃ * (1 - s₁ - s₃))
              - b₃ * (-(b₁ * b₂ * (1 - s₁ - s₂)))
              - w + g * u + g * v + g := by
                linear_combination
                  -b₁ * htriple₂₃ + b₂ * htriple₁₃ - b₃ * htriple₁₂
        _ = p * (1 - (s₁ + s₂ + s₃)) - w + g * u + g * v + g := by
              simp only [p]
              ring
    rw [← hshape]
    exact hdet
  have hfull : w - g * (u + v) = g + p * (1 - (s₁ + s₂ + s₃)) := by
    nlinarith [hdetRewrite]
  have hprod : u * v * w = p * ((1 - s₁) * (1 - s₂) * (1 - s₃)) := by
    calc
      u * v * w = (r₀ * c₀) * (r₁ * c₁) * (r₂ * c₂) := by
        dsimp only [u, v, w]
        ring
      _ = (b₁ * (1 - s₁)) * (b₂ * (1 - s₂)) * (b₃ * (1 - s₃)) := by
        rw [hpair₁, hpair₂, hpair₃]
      _ = p * ((1 - s₁) * (1 - s₂) * (1 - s₃)) := by
        dsimp only [p]
        ring
  exact stationaryCycleFace_product_impossible g p s₁ s₂ s₃ u v w hg
    hs₁ hs₂ hs₃ hsum huEq hvEq hwEq hprod hfull

end DUnstableCores
