import Mathlib

/-!
# The attainable-region inequality (sharp form)

For pieces `0 ≤ x_j ≤ r_j` with total `X = Σ x_j` lying in an interval `(a, b)` that contains no
subset sum of `r`,

  `(X - a)(b - X) ≤ (Σ_j √(x_j (r_j - x_j)))²`.

Geometrically: the semicircle heights of the pieces add up to at least the semicircle erected over
the subset-sum gap containing `X`.  Proof by strong induction on the number of fractional pieces,
using a two-piece exchange along which the height sum is concave (so it is minimized at an
endpoint, where one more piece is at a bound).
-/

namespace DStabilityHardness

open scoped BigOperators

noncomputable section

/-- Semicircle height of a piece of size `r` carrying load `x`. -/
def semi (x r : ℝ) : ℝ := Real.sqrt (x * (r - x))

theorem sqrt_combo (A B μ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    μ * Real.sqrt A + (1 - μ) * Real.sqrt B ≤ Real.sqrt (μ * A + (1 - μ) * B) := by
  have sA := Real.sq_sqrt hA
  have sB := Real.sq_sqrt hB
  have hsA := Real.sqrt_nonneg A
  have hsB := Real.sqrt_nonneg B
  have key : (μ * Real.sqrt A + (1 - μ) * Real.sqrt B) ^ 2 ≤ μ * A + (1 - μ) * B := by
    have h1 : 0 ≤ μ * (1 - μ) := mul_nonneg hμ0 (by linarith)
    nlinarith [mul_nonneg h1 (sq_nonneg (Real.sqrt A - Real.sqrt B))]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt key)

/-- Concavity of a semicircle height along a segment through `0`. -/
theorem semi_concave (x r s0 s1 : ℝ) (h0 : s0 ≤ 0) (h1 : 0 ≤ s1) (hlt : s0 < s1)
    (hr0 : 0 ≤ x + s0) (hr1 : x + s1 ≤ r) :
    s1 / (s1 - s0) * semi (x + s0) r + (1 - s1 / (s1 - s0)) * semi (x + s1) r ≤ semi x r := by
  have hd : 0 < s1 - s0 := by linarith
  set μ := s1 / (s1 - s0) with hμ
  have hμ0 : 0 ≤ μ := div_nonneg h1 hd.le
  have hμ1 : μ ≤ 1 := by rw [hμ, div_le_one hd]; linarith
  have hA : 0 ≤ (x + s0) * (r - (x + s0)) := mul_nonneg hr0 (by linarith)
  have hB : 0 ≤ (x + s1) * (r - (x + s1)) := mul_nonneg (by linarith) (by linarith)
  have hcomb := sqrt_combo _ _ μ hA hB hμ0 hμ1
  have hq : μ * ((x + s0) * (r - (x + s0))) + (1 - μ) * ((x + s1) * (r - (x + s1)))
      ≤ x * (r - x) := by
    have e : x * (r - x) - (μ * ((x + s0) * (r - (x + s0))) + (1 - μ) * ((x + s1) * (r - (x + s1))))
        = μ * (1 - μ) * (s1 - s0) ^ 2 := by
      have hμs : μ * s0 + (1 - μ) * s1 = 0 := by
        rw [hμ]; field_simp; ring
      have : s1 = -(μ * s0) / (1 - μ) ∨ μ = 1 := by
        rcases eq_or_ne μ 1 with h | h
        · exact Or.inr h
        · left; field_simp [sub_ne_zero.mpr (Ne.symm h)]; linarith
      nlinarith [hμs]
    nlinarith [mul_nonneg (mul_nonneg hμ0 (by linarith : (0 : ℝ) ≤ 1 - μ)) (sq_nonneg (s1 - s0))]
  unfold semi
  exact le_trans hcomb (Real.sqrt_le_sqrt hq)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The fractional pieces. -/
def fracSet (r x : κ → ℝ) : Finset κ := Finset.univ.filter (fun j => 0 < x j ∧ x j < r j)

/-- Exchange `s` units of load from piece `k` to piece `j`. -/
def shiftPair (x : κ → ℝ) (j k : κ) (s : ℝ) : κ → ℝ :=
  fun i => if i = j then x j + s else if i = k then x k - s else x i

omit [Fintype κ] in
theorem shiftPair_j (x : κ → ℝ) (j k : κ) (s : ℝ) : shiftPair x j k s j = x j + s := by
  simp [shiftPair]

omit [Fintype κ] in
theorem shiftPair_k (x : κ → ℝ) (j k : κ) (hjk : j ≠ k) (s : ℝ) : shiftPair x j k s k = x k - s := by
  simp [shiftPair, hjk.symm]

theorem sum_shiftPair (x : κ → ℝ) (j k : κ) (hjk : j ≠ k) (s : ℝ) :
    ∑ i, shiftPair x j k s i = ∑ i, x i := by
  have h : ∑ i, (shiftPair x j k s i - x i) = 0 := by
    rw [Fintype.sum_eq_add j k hjk]
    · simp [shiftPair, hjk.symm]
    · intro c hc
      simp [shiftPair, hc.1, hc.2]
  rw [Finset.sum_sub_distrib] at h
  linarith

theorem heights_shiftPair (r x : κ → ℝ) (j k : κ) (hjk : j ≠ k) (s : ℝ) :
    ∑ i, semi (shiftPair x j k s i) (r i) =
      ∑ i, semi (x i) (r i) + (semi (x j + s) (r j) - semi (x j) (r j))
        + (semi (x k - s) (r k) - semi (x k) (r k)) := by
  have h : ∑ i, (semi (shiftPair x j k s i) (r i) - semi (x i) (r i)) =
      (semi (x j + s) (r j) - semi (x j) (r j)) + (semi (x k - s) (r k) - semi (x k) (r k)) := by
    rw [Fintype.sum_eq_add j k hjk]
    · simp [shiftPair, hjk.symm]
    · intro c hc
      simp [shiftPair, hc.1, hc.2]
  rw [Finset.sum_sub_distrib] at h
  linarith

/-- **Attainable-region inequality.** -/
theorem attainable (r : κ → ℝ) (hr : ∀ j, 0 < r j) (a b : ℝ)
    (hgap : ∀ S : Finset κ, ¬ (a < ∑ j ∈ S, r j ∧ ∑ j ∈ S, r j < b)) :
    ∀ n : ℕ, ∀ x : κ → ℝ, (fracSet r x).card = n → (∀ j, 0 ≤ x j ∧ x j ≤ r j) →
      a < ∑ j, x j → ∑ j, x j < b →
      (∑ j, x j - a) * (b - ∑ j, x j) ≤ (∑ j, semi (x j) (r j)) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hcard hx ha hb
  have hsemi_nonneg : ∀ y : κ → ℝ, 0 ≤ ∑ j, semi (y j) (r j) :=
    fun y => Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
  -- pieces outside the fractional set sit at a bound
  have hbound : ∀ j, j ∉ fracSet r x → x j = 0 ∨ x j = r j := by
    intro j hj
    simp only [fracSet, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_lt] at hj
    rcases hj with h | h
    · left; linarith [(hx j).1]
    · right; linarith [(hx j).2]
  by_cases htwo : ∃ j ∈ fracSet r x, ∃ k ∈ fracSet r x, j ≠ k
  · -- exchange step
    obtain ⟨j, hj, k, hk, hjk⟩ := htwo
    have hj' := (Finset.mem_filter.mp hj).2
    have hk' := (Finset.mem_filter.mp hk).2
    set s0 := -(min (x j) (r k - x k)) with hs0
    set s1 := min (r j - x j) (x k) with hs1
    have hs0n : s0 < 0 := by
      rw [hs0]; have : 0 < min (x j) (r k - x k) := lt_min hj'.1 (by linarith [hk'.2])
      linarith
    have hs1p : 0 < s1 := lt_min (by linarith [hj'.2]) hk'.1
    have hlt : s0 < s1 := by linarith
    -- endpoints stay in range and reduce the fractional set
    have hrange : ∀ s, s0 ≤ s → s ≤ s1 → ∀ i, 0 ≤ shiftPair x j k s i ∧ shiftPair x j k s i ≤ r i := by
      intro s h0 h1 i
      have m1 := min_le_left (x j) (r k - x k)
      have m2 := min_le_right (x j) (r k - x k)
      have m3 := min_le_left (r j - x j) (x k)
      have m4 := min_le_right (r j - x j) (x k)
      unfold shiftPair
      by_cases hij : i = j
      · subst hij; simp; constructor <;> linarith
      · by_cases hik : i = k
        · subst hik; simp [hij]; constructor <;> linarith
        · simp [hij, hik]; exact hx i
    have hsub : ∀ s, s0 ≤ s → s ≤ s1 → fracSet r (shiftPair x j k s) ⊆ fracSet r x := by
      intro s h0 h1 i hi
      simp only [fracSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_cases hij : i = j
      · subst hij; exact hj'
      · by_cases hik : i = k
        · subst hik; exact hk'
        · simpa [shiftPair, hij, hik] using hi
    have hdrop : ∀ s ∈ ({s0, s1} : Set ℝ),
        (fracSet r (shiftPair x j k s)).card < (fracSet r x).card := by
      intro s hs
      have hs' : s0 ≤ s ∧ s ≤ s1 := by
        rcases hs with h | h <;> (rw [h]; constructor <;> linarith)
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub s hs'.1 hs'.2, ?_⟩
      intro heq
      have hjin : j ∈ fracSet r (shiftPair x j k s) := heq ▸ hj
      have hkin : k ∈ fracSet r (shiftPair x j k s) := heq ▸ hk
      have hj2 := (Finset.mem_filter.mp hjin).2
      have hk2 := (Finset.mem_filter.mp hkin).2
      rw [shiftPair_j] at hj2
      rw [shiftPair_k x j k hjk] at hk2
      have m1 := min_le_left (x j) (r k - x k)
      have m2 := min_le_right (x j) (r k - x k)
      have m3 := min_le_left (r j - x j) (x k)
      have m4 := min_le_right (r j - x j) (x k)
      rcases hs with h | h
      · rw [h] at hj2 hk2
        rcases le_total (x j) (r k - x k) with hm | hm
        · have : s0 = -(x j) := by rw [hs0, min_eq_left hm]
          rw [this] at hj2; linarith [hj2.1]
        · have : s0 = -(r k - x k) := by rw [hs0, min_eq_right hm]
          rw [this] at hk2; linarith [hk2.2]
      · have h' : s = s1 := h
        rw [h'] at hj2 hk2
        rcases le_total (r j - x j) (x k) with hm | hm
        · have : s1 = r j - x j := by rw [hs1, min_eq_left hm]
          rw [this] at hj2; linarith [hj2.2]
        · have : s1 = x k := by rw [hs1, min_eq_right hm]
          rw [this] at hk2; linarith [hk2.1]
    -- the height sum is concave along the exchange
    have hcj := semi_concave (x j) (r j) s0 s1 hs0n.le hs1p.le hlt
      (by have := min_le_left (x j) (r k - x k); rw [hs0]; linarith)
      (by have := min_le_left (r j - x j) (x k); rw [hs1]; linarith)
    have hck := semi_concave (x k) (r k) (-s1) (-s0) (by linarith) (by linarith) (by linarith)
      (by have := min_le_right (r j - x j) (x k); rw [hs1]; linarith)
      (by have := min_le_right (x j) (r k - x k); rw [hs0]; linarith)
    set μ := s1 / (s1 - s0) with hμ
    have hdne : s1 - s0 ≠ 0 := (by linarith : (0 : ℝ) < s1 - s0).ne'
    have hμ' : (-s0) / ((-s0) - (-s1)) = 1 - μ := by
      have e : (-s0) - (-s1) = s1 - s0 := by ring
      rw [e, hμ]; field_simp; ring
    rw [hμ'] at hck
    have e1 : x k + -s1 = x k - s1 := by ring
    have e2 : x k + -s0 = x k - s0 := by ring
    rw [e1, e2] at hck
    have hμ0 : 0 ≤ μ := div_nonneg hs1p.le (by linarith)
    have hμ1 : μ ≤ 1 := by rw [hμ, div_le_one (by linarith)]; linarith
    set H := ∑ i, semi (x i) (r i)
    have H0 := heights_shiftPair r x j k hjk s0
    have H1 := heights_shiftPair r x j k hjk s1
    have hmin : min (∑ i, semi (shiftPair x j k s0 i) (r i)) (∑ i, semi (shiftPair x j k s1 i) (r i))
        ≤ H := by
      have hconv : μ * (∑ i, semi (shiftPair x j k s0 i) (r i)) +
          (1 - μ) * (∑ i, semi (shiftPair x j k s1 i) (r i)) ≤ H := by
        rw [H0, H1]
        nlinarith
      have hm0 := min_le_left (∑ i, semi (shiftPair x j k s0 i) (r i))
        (∑ i, semi (shiftPair x j k s1 i) (r i))
      have hm1 := min_le_right (∑ i, semi (shiftPair x j k s0 i) (r i))
        (∑ i, semi (shiftPair x j k s1 i) (r i))
      nlinarith
    -- apply the induction hypothesis at the better endpoint
    have hIH : ∀ s ∈ ({s0, s1} : Set ℝ),
        (∑ i, x i - a) * (b - ∑ i, x i) ≤ (∑ i, semi (shiftPair x j k s i) (r i)) ^ 2 := by
      intro s hs
      have hs' : s0 ≤ s ∧ s ≤ s1 := by
        rcases hs with h | h <;> (rw [h]; constructor <;> linarith)
      have hsum := sum_shiftPair x j k hjk s
      have := ih _ (hcard ▸ hdrop s hs) (shiftPair x j k s) rfl (hrange s hs'.1 hs'.2)
        (by rw [hsum]; exact ha) (by rw [hsum]; exact hb)
      rwa [hsum] at this
    have hI0 := hIH s0 (Or.inl rfl)
    have hI1 := hIH s1 (Or.inr rfl)
    have hHn := hsemi_nonneg x
    rcases min_choice (∑ i, semi (shiftPair x j k s0 i) (r i))
        (∑ i, semi (shiftPair x j k s1 i) (r i)) with h | h
    · rw [h] at hmin
      have := hsemi_nonneg (shiftPair x j k s0)
      nlinarith
    · rw [h] at hmin
      have := hsemi_nonneg (shiftPair x j k s1)
      nlinarith
  · -- at most one fractional piece
    push Not at htwo
    let S : Finset κ := Finset.univ.filter (fun i => i ∉ fracSet r x ∧ x i = r i)
    have hxsplit : ∀ i, x i = (if i ∈ S then r i else 0) + (if i ∈ fracSet r x then x i else 0) := by
      intro i
      by_cases hi : i ∈ fracSet r x
      · have : i ∉ S := by simp [S, hi]
        simp [hi, this]
      · rcases hbound i hi with h | h
        · have : i ∉ S := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
            intro _ hh; rw [h] at hh; linarith [hr i]
          simp [hi, this, h]
        · have : i ∈ S := by simp [S, hi, h]
          simp [hi, this, h]
    have hX : ∑ i, x i = ∑ i ∈ S, r i + ∑ i ∈ fracSet r x, x i := by
      rw [Finset.sum_congr rfl (fun i _ => hxsplit i), Finset.sum_add_distrib, Finset.sum_ite_mem,
        Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]
    have hsemi_split : ∑ i, semi (x i) (r i) = ∑ i ∈ fracSet r x, semi (x i) (r i) := by
      rw [← Finset.sum_subset (Finset.subset_univ (fracSet r x))]
      intro i _ hi
      unfold semi
      rcases hbound i hi with h | h <;> simp [h]
    rcases Nat.lt_or_ge (fracSet r x).card 2 with hc | hc
    · interval_cases hcc : (fracSet r x).card
      · -- no fractional piece: the total is a subset sum
        have hempty : fracSet r x = ∅ := Finset.card_eq_zero.mp hcc
        rw [hempty, Finset.sum_empty, add_zero] at hX
        exact absurd ⟨by rw [← hX]; exact ha, by rw [← hX]; exact hb⟩ (hgap S)
      · obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcc
        rw [hk, Finset.sum_singleton] at hX
        rw [hsemi_split, hk, Finset.sum_singleton]
        have hkS : k ∉ S := by simp [S, hk]
        have hlow := hgap S
        have hhigh := hgap (insert k S)
        rw [Finset.sum_insert hkS] at hhigh
        have hxk := hx k
        have hSle : ∑ i ∈ S, r i ≤ a := by
          by_contra h; push Not at h
          exact hlow ⟨h, by linarith [hxk.1]⟩
        have hShi : b ≤ r k + ∑ i ∈ S, r i := by
          by_contra h; push Not at h
          exact hhigh ⟨by linarith [hxk.2], h⟩
        unfold semi
        rw [Real.sq_sqrt (mul_nonneg hxk.1 (by linarith [hxk.2]))]
        rw [hX]
        have h1 : 0 ≤ ∑ i ∈ S, r i + x k - a := by linarith
        have h2 : 0 ≤ b - (∑ i ∈ S, r i + x k) := by linarith
        nlinarith
    · exfalso
      obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hc
      exact hjk (htwo j hj k hk)

end

end DStabilityHardness
