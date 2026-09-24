import proofs.InheritedCellAssay.ScalarCountDecision
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases

namespace InheritedCellAssay.ScalarCount

noncomputable def countMajorant (n : ℕ) : ℝ :=
  (64/21) * (1 - 7*(1/2)^n + 14*(1/4)^n - 8*(1/8)^n)

theorem countMajorant_bounds (n : ℕ) :
    (if n < 3 then (0 : ℝ) else 1) ≤ countMajorant n := by
  by_cases hn : n < 3
  · interval_cases n <;> norm_num [countMajorant]
  · have hx : (1/2 : ℝ)^n ≤ 1/8 := by
      have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) ≤ 1) (by omega : 3 ≤ n)
      norm_num at h
      exact h
    have h4 : (1/4 : ℝ)^n = ((1/2 : ℝ)^n)^2 := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    have h8 : (1/8 : ℝ)^n = ((1/2 : ℝ)^n)^3 := by
      rw [← pow_mul, Nat.mul_comm n 3, pow_mul]
      norm_num
    have hp : (7/8 : ℝ)*(3/4)*(1/2) ≤
        (1-(1/2 : ℝ)^n)*(1-2*(1/2 : ℝ)^n)*(1-4*(1/2 : ℝ)^n) := by
      gcongr <;> nlinarith [sq_nonneg ((1/2 : ℝ)^n)]
    simp only [hn, ↓reduceIte, countMajorant, h4, h8]
    nlinarith [hp]

/-- Three bounded PGF observations suffice to control the probability of count
    at least three. No geometric-distribution premise is used. -/
theorem coverage_from_three_pgf (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hn : HasSum w 1) (a b c : ℝ)
    (ha : HasSum (fun n => w n*(1/2)^n) a)
    (hb : HasSum (fun n => w n*(1/4)^n) b)
    (hc : HasSum (fun n => w n*(1/8)^n) c) :
    1 - (64/21)*(1-7*a+14*b-8*c) ≤ w 0+w 1+w 2 := by
  have hs : HasSum (fun n => w n*countMajorant n)
      ((64/21)*(1-7*a+14*b-8*c)) := by
    convert (((hn.sub (ha.mul_left 7)).add (hb.mul_left 14)).sub
      (hc.mul_left 8)).mul_left (64/21) using 1
    ext n
    unfold countMajorant
    ring
  have hf : HasSum (fun n => if n < 3 then w n else 0) (w 0+w 1+w 2) := by
    have h := hasSum_sum_of_ne_finset_zero (s := Finset.range 3) (L := .unconditional ℕ)
      (f := fun n => if n < 3 then w n else 0)
      (fun n hn => by simp only [Finset.mem_range] at hn; simp [hn])
    simpa [Finset.sum_range_succ] using h
  have hle : ∀ n, w n ≤ (if n < 3 then w n else 0) + w n*countMajorant n := by
    intro n
    have h := countMajorant_bounds n
    split_ifs with hh
    · simp only [hh, ↓reduceIte] at h
      nlinarith [mul_nonneg (hw n) h]
    · simp only [hh, ↓reduceIte] at h
      nlinarith [mul_nonneg (hw n) (sub_nonneg.mpr h)]
  have hh := hasSum_le hle hn (hf.add hs)
  linarith

noncomputable def proposedPGFHalf : ℝ :=
  1 - (33/64)*geometricParameter/(geometricParameter+1)
noncomputable def proposedPGFQuarter : ℝ :=
  1 - 3*(33/64)*geometricParameter/(geometricParameter+3)
noncomputable def proposedPGFEighth : ℝ :=
  1 - 7*(33/64)*geometricParameter/(geometricParameter+7)

theorem three_pgf_small :
    (64/21)*(1-7*proposedPGFHalf+14*proposedPGFQuarter-8*proposedPGFEighth) < 1/20 := by
  obtain ⟨hl, hu⟩ := geometricParameter_bounds
  have hp : 0 ≤ geometricParameter := by linarith
  have h1 : geometricParameter+1 ≠ 0 := by positivity
  have h3 : geometricParameter+3 ≠ 0 := by positivity
  have h7 : geometricParameter+7 ≠ 0 := by positivity
  have he : (64/21)*(1-7*proposedPGFHalf+14*proposedPGFQuarter-8*proposedPGFEighth) =
      33*geometricParameter*(1-geometricParameter)^2 /
        ((geometricParameter+1)*(geometricParameter+3)*(geometricParameter+7)) := by
    unfold proposedPGFHalf proposedPGFQuarter proposedPGFEighth
    field_simp [h1, h3, h7]
    ring
  rw [he]
  have hd : 32 ≤ (geometricParameter+1)*(geometricParameter+3)*(geometricParameter+7) := by
    have h : (3/2 : ℝ)*(7/2)*(15/2) ≤
        (geometricParameter+1)*(geometricParameter+3)*(geometricParameter+7) := by
      gcongr <;> linarith
    linarith
  apply (div_lt_iff₀ (by linarith :
    0 < (geometricParameter+1)*(geometricParameter+3)*(geometricParameter+7))).mpr
  have ht := scalar_two_tail_small
  unfold scalarTail at ht
  nlinarith

/-- The unresolved source task is reduced to three explicit bounded PGFs. -/
theorem scalar_coverage_of_three_pgf (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hn : HasSum w 1)
    (ha : HasSum (fun n => w n*(1/2)^n) proposedPGFHalf)
    (hb : HasSum (fun n => w n*(1/4)^n) proposedPGFQuarter)
    (hc : HasSum (fun n => w n*(1/8)^n) proposedPGFEighth) :
    19/20 < w 0+w 1+w 2 := by
  have h := coverage_from_three_pgf w hw hn _ _ _ ha hb hc
  have hs := three_pgf_small
  linarith

end InheritedCellAssay.ScalarCount
