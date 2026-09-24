import proofs.FunctionalViability.ExtendedCoverage

namespace FunctionalViability.Robust
noncomputable section

/-! ## Exact worst-case response of every fixed allocation

For allocation weight `w`, write `A = |2w-1|`, `h = hRange c` and
`t = min d h`. The worst admissible source has three regimes. -/

def profileCore (c h t A : ℝ) : ℝ :=
  if A*c ≤ h-t then (c^2-t^2-A^2*c^2)/4
  else if A*c ≤ h then (c^2+h^2-2*h*t-2*A*c*(h-t))/4
  else (c^2+h^2-2*A*c*h)/4

def allocationFloor (c d w : ℝ) : ℝ :=
  profileCore c (hRange c) (min d (hRange c)) |2*w-1|

/-- One-dimensional core: `v` is the absolute balance coordinate, `T` the squared
mismatch, which is limited both by `t^2` and by the remaining width `(h-v)^2`. -/
theorem profile_core_lower (c h t A v T : ℝ) (hvh : v ≤ h)
    (hTt : T ≤ t^2) (hTh : T ≤ (h-v)^2) :
    profileCore c h t A ≤ (v^2+c^2-T-2*A*c*v)/4 := by
  unfold profileCore
  split_ifs with h1 h2
  · nlinarith [sq_nonneg (v-A*c)]
  · have h1' : h-t < A*c := not_le.mp h1
    rcases le_total v (h-t) with hv' | hv'
    · nlinarith [mul_nonneg (show (0:ℝ) ≤ h-t-v by linarith)
        (show (0:ℝ) ≤ 2*A*c-v-(h-t) by linarith)]
    · nlinarith [mul_nonneg (show (0:ℝ) ≤ h-A*c by linarith)
        (show (0:ℝ) ≤ v-(h-t) by linarith)]
  · have h2' : h < A*c := not_le.mp h2
    nlinarith [mul_nonneg (show (0:ℝ) ≤ A*c-h by linarith)
      (show (0:ℝ) ≤ h-v by linarith)]

theorem allocation_lower (c d w x y a b : ℝ) (hc : 0 ≤ c)
    (hw : 0 ≤ w ∧ w ≤ 1) (h : Admissible c d x y a b) :
    allocationFloor c d w ≤ w*(x*y)+(1-w)*(a*b) := by
  rcases h with ⟨hx, hy, ha, hb, hca, hcb, hd⟩
  obtain ⟨X, Y, hle, hX, hY, hXY⟩ : ∃ X Y : ℝ,
      w*(X*Y)+(1-w)*((c-X)*(c-Y)) ≤ w*(x*y)+(1-w)*(a*b) ∧
      |2*X-c| ≤ hRange c ∧ |2*Y-c| ≤ hRange c ∧ |X-Y| ≤ d := by
    rcases le_total c 1 with h1 | h1
    · have hh : hRange c = c := min_eq_left (by linarith)
      have hX0 : 0 ≤ min x c := le_min hx.1 hc
      have hY0 : 0 ≤ min y c := le_min hy.1 hc
      have hXc : min x c ≤ c := min_le_right _ _
      have hYc : min y c ≤ c := min_le_right _ _
      refine ⟨min x c, min y c, ?_, ?_, ?_, clipped_mismatch x y c d hd⟩
      · have hXa : c-min x c ≤ a := by
          by_cases ht : x ≤ c
          · rw [min_eq_left ht]; linarith
          · rw [min_eq_right (le_of_not_ge ht)]; linarith [ha.1]
        have hYb : c-min y c ≤ b := by
          by_cases ht : y ≤ c
          · rw [min_eq_left ht]; linarith
          · rw [min_eq_right (le_of_not_ge ht)]; linarith [hb.1]
        have hxy : min x c*min y c ≤ x*y :=
          mul_le_mul (min_le_left _ _) (min_le_left _ _) hY0 hx.1
        have hab : (c-min x c)*(c-min y c) ≤ a*b :=
          mul_le_mul hXa hYb (by linarith) ha.1
        have h1' := mul_le_mul_of_nonneg_left hxy hw.1
        have h2' := mul_le_mul_of_nonneg_left hab (show (0:ℝ) ≤ 1-w by linarith [hw.2])
        linarith
      · rw [hh, abs_le]; constructor <;> linarith
      · rw [hh, abs_le]; constructor <;> linarith
    · have hh : hRange c = 2-c := min_eq_right (by linarith)
      refine ⟨x, y, ?_, ?_, ?_, hd⟩
      · have hab : (c-x)*(c-y) ≤ a*b :=
          mul_le_mul (by linarith) (by linarith) (by linarith [hy.2]) ha.1
        have h2' := mul_le_mul_of_nonneg_left hab (show (0:ℝ) ≤ 1-w by linarith [hw.2])
        linarith
      · rw [hh, abs_le]; constructor <;> linarith [ha.2, hx.2]
      · rw [hh, abs_le]; constructor <;> linarith [hb.2, hy.2]
  have hsum : |X+Y-c|+|X-Y| ≤ hRange c := by
    rcases abs_le.mp hX with ⟨a1, a2⟩
    rcases abs_le.mp hY with ⟨b1, b2⟩
    rcases le_total 0 (X+Y-c) with p | p <;> rcases le_total 0 (X-Y) with q | q
    · rw [abs_of_nonneg p, abs_of_nonneg q]; linarith
    · rw [abs_of_nonneg p, abs_of_nonpos q]; linarith
    · rw [abs_of_nonpos p, abs_of_nonneg q]; linarith
    · rw [abs_of_nonpos p, abs_of_nonpos q]; linarith
  have hv0 := abs_nonneg (X+Y-c)
  have hτ0 := abs_nonneg (X-Y)
  have hτt : (X-Y)^2 ≤ (min d (hRange c))^2 := by
    have h1 : |X-Y| ≤ min d (hRange c) := le_min hXY (by linarith)
    nlinarith [sq_abs (X-Y), mul_nonneg (show (0:ℝ) ≤ min d (hRange c)-|X-Y| by linarith)
      (show (0:ℝ) ≤ min d (hRange c)+|X-Y| by linarith)]
  have hτh : (X-Y)^2 ≤ (hRange c-|X+Y-c|)^2 := by
    nlinarith [sq_abs (X-Y), mul_nonneg (show (0:ℝ) ≤ hRange c-|X+Y-c|-|X-Y| by linarith)
      (show (0:ℝ) ≤ hRange c-|X+Y-c|+|X-Y| by linarith)]
  have hsign : -(|2*w-1| *c*|X+Y-c|) ≤ (2*w-1)*c*(X+Y-c) := by
    have h0 := neg_abs_le ((2*w-1)*(X+Y-c))
    rw [abs_mul] at h0
    have h1 := mul_le_mul_of_nonneg_left h0 hc
    have e1 : c*(-(|2*w-1| *|X+Y-c|)) = -(|2*w-1| *c*|X+Y-c|) := by ring
    have e2 : c*((2*w-1)*(X+Y-c)) = (2*w-1)*c*(X+Y-c) := by ring
    linarith
  have hcore := profile_core_lower c (hRange c) (min d (hRange c)) |2*w-1| |X+Y-c|
    ((X-Y)^2) (by linarith) hτt hτh
  have hid : w*(X*Y)+(1-w)*((c-X)*(c-Y))
      = ((X+Y-c)^2+c^2-(X-Y)^2+2*((2*w-1)*c*(X+Y-c)))/4 := by ring
  have hv2 : |X+Y-c|^2 = (X+Y-c)^2 := sq_abs _
  unfold allocationFloor
  linarith

/-- A family of admissible sources parameterised by balance `σ` and mismatch `τ`. -/
theorem profile_witness (c d w σ τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτd : τ ≤ d) (hs1 : σ+τ ≤ hRange c) (hs2 : -σ+τ ≤ hRange c) :
    Admissible c d ((c+σ+τ)/2) ((c+σ-τ)/2) ((c-σ-τ)/2) ((c-σ+τ)/2) ∧
    w*(((c+σ+τ)/2)*((c+σ-τ)/2))+(1-w)*(((c-σ-τ)/2)*((c-σ+τ)/2))
      = (σ^2+c^2-τ^2+2*((2*w-1)*c*σ))/4 := by
  have hl := hRange_le_left c
  have hr := hRange_le_right c
  refine ⟨?_, by ring⟩
  unfold Admissible
  have he : (c+σ+τ)/2-(c+σ-τ)/2 = τ := by ring
  rw [he, abs_of_nonneg hτ0]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    by linarith, by linarith, hτd⟩

theorem allocation_attained (c d w : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 2) (hd : 0 ≤ d) :
    ∃ x y a b, Admissible c d x y a b ∧
      w*(x*y)+(1-w)*(a*b) = allocationFloor c d w := by
  have hh0 := hRange_nonneg c hc hc2
  have ht0 := mismatch_nonneg c d hc hc2 hd
  have hth : min d (hRange c) ≤ hRange c := min_le_right _ _
  have htd := mismatch_le_d c d
  have hAc : 0 ≤ |2*w-1| *c := mul_nonneg (abs_nonneg _) hc
  obtain ⟨v, τ, hv0, hτ0, hτd, hvτ, hval⟩ : ∃ v τ : ℝ, 0 ≤ v ∧ 0 ≤ τ ∧ τ ≤ d ∧
      v+τ ≤ hRange c ∧ allocationFloor c d w = (v^2+c^2-τ^2-2*|2*w-1| *c*v)/4 := by
    unfold allocationFloor profileCore
    split_ifs with h1 h2
    · exact ⟨|2*w-1| *c, min d (hRange c), hAc, ht0, htd, by linarith, by ring⟩
    · exact ⟨hRange c-min d (hRange c), min d (hRange c), by linarith, ht0, htd,
        by linarith, by ring⟩
    · exact ⟨hRange c, 0, hh0, le_refl 0, hd, by linarith, by ring⟩
  rcases le_total 0 (2*w-1) with hs | hs
  · obtain ⟨hadm, heq⟩ := profile_witness c d w (-v) τ hτ0 hτd (by linarith) (by linarith)
    refine ⟨_, _, _, _, hadm, ?_⟩
    rw [heq, hval, abs_of_nonneg hs]; ring
  · obtain ⟨hadm, heq⟩ := profile_witness c d w v τ hτ0 hτd (by linarith) (by linarith)
    refine ⟨_, _, _, _, hadm, ?_⟩
    rw [heq, hval, abs_of_nonpos hs]; ring

/-- Exact allocation profile: the lower bound holds for every admissible source and
is attained by one. -/
theorem allocation_profile (c d w : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 2) (hd : 0 ≤ d)
    (hw : 0 ≤ w ∧ w ≤ 1) :
    (∀ x y a b, Admissible c d x y a b → allocationFloor c d w ≤ w*(x*y)+(1-w)*(a*b)) ∧
    (∃ x y a b, Admissible c d x y a b ∧ w*(x*y)+(1-w)*(a*b) = allocationFloor c d w) :=
  ⟨fun x y a b h => allocation_lower c d w x y a b hc hw h,
   allocation_attained c d w hc hc2 hd⟩

theorem allocation_half (c d : ℝ) : allocationFloor c d (1/2) = extendedFloor c d := by
  unfold allocationFloor profileCore extendedFloor
  have h0 : |2*(1/2:ℝ)-1| = 0 := by norm_num
  have hle : (0:ℝ)*c ≤ hRange c-min d (hRange c) := by
    rw [zero_mul]; linarith [min_le_right d (hRange c)]
  rw [h0, if_pos hle]
  ring

/-- Strict loss away from equal allocation whenever the mismatch budget is binding
below the attainable width. -/
theorem allocation_strict (c d w : ℝ) (hc : 0 < c) (hc2 : c ≤ 2) (hd : 0 ≤ d)
    (hbind : min d (hRange c) < hRange c) (hw : w ≠ 1/2) :
    allocationFloor c d w < extendedFloor c d := by
  have hA : 0 < |2*w-1| := abs_pos.mpr (by intro h; apply hw; linarith)
  have hAc : 0 < |2*w-1| *c := mul_pos hA hc
  have ht0 := mismatch_nonneg c d hc.le hc2 hd
  unfold allocationFloor profileCore extendedFloor
  split_ifs with h1 h2
  · nlinarith [mul_pos hAc hAc]
  · have h1' := not_le.mp h1
    nlinarith [mul_pos (show (0:ℝ) < hRange c-min d (hRange c) by linarith)
      (show (0:ℝ) < 2*|2*w-1| *c-(hRange c-min d (hRange c)) by linarith)]
  · have h2' := not_le.mp h2
    nlinarith [mul_nonneg (show (0:ℝ) ≤ hRange c by linarith)
      (show (0:ℝ) ≤ |2*w-1| *c-hRange c by linarith),
      mul_pos (show (0:ℝ) < hRange c-min d (hRange c) by linarith)
      (show (0:ℝ) < hRange c+min d (hRange c) by linarith)]

/-- When the mismatch budget does not bind, every allocation with
`|2w-1| c ≤ hRange c` is maximin: the optimum is a plateau. -/
theorem allocation_plateau (c d w : ℝ) (hc : 0 ≤ c) (hbind : hRange c ≤ d)
    (hw : |2*w-1| * c ≤ hRange c) :
    allocationFloor c d w = extendedFloor c d := by
  have ht : min d (hRange c) = hRange c := min_eq_right hbind
  have hA0 : 0 ≤ |2*w-1| * c := mul_nonneg (abs_nonneg _) hc
  unfold allocationFloor profileCore extendedFloor
  rw [ht]
  split_ifs with h1
  · have hz : |2*w-1| * c = 0 := le_antisymm (by linarith) hA0
    have hz2 : |2*w-1|^2*c^2 = 0 := by rw [← mul_pow, hz]; norm_num
    linarith
  · ring
/-! ## Finite feasibility of the calibrated all-negative certificate -/

/-- With per-unit least detectable probability `z`, a finite balanced design meets
total error `alpha` exactly in the two stated regimes. -/
theorem finite_feasibility (z delta alpha : ℝ) (hz : 0 ≤ z ∧ z ≤ 1)
    (hd : 0 ≤ delta ∧ delta ≤ 1) (ha : 0 < alpha ∧ alpha < 1) :
    (∃ m : ℕ, 0 < m ∧ delta+(1-delta)*(1-z)^(2*m) ≤ alpha) ↔
      ((0 < z ∧ delta < alpha) ∨ (z = 1 ∧ delta ≤ alpha)) := by
  constructor
  · rintro ⟨m, hm, hb⟩
    have hq0 : 0 ≤ (1-z)^(2*m) := pow_nonneg (by linarith [hz.2]) _
    rcases lt_or_ge delta alpha with hlt | hge
    · left
      refine ⟨?_, hlt⟩
      by_contra hz0
      have hz' : z = 0 := le_antisymm (not_lt.mp hz0) hz.1
      rw [hz', sub_zero, one_pow] at hb
      linarith [ha.2]
    · right
      have hpn : 0 ≤ (1-delta)*(1-z)^(2*m) := mul_nonneg (by linarith [hd.2]) hq0
      have hd1 : 0 < 1-delta := by linarith [ha.2]
      have hprod : (1-delta)*(1-z)^(2*m) ≤ (1-delta)*0 := by linarith
      have hq' : (1-z)^(2*m) ≤ 0 := le_of_mul_le_mul_left hprod hd1
      have hq : (1-z)^(2*m) = 0 := le_antisymm hq' hq0
      have h1z : 1-z = 0 := (pow_eq_zero_iff (by omega)).mp hq
      rw [hq, mul_zero, add_zero] at hb
      exact ⟨by linarith, hb⟩
  · rintro (⟨hz0, hlt⟩ | ⟨hz1, hle⟩)
    · have hε : 0 < alpha-delta := by linarith
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (show 1-z < 1 by linarith)
      refine ⟨n+1, by omega, ?_⟩
      have hmono : (1-z)^(2*(n+1)) ≤ (1-z)^n :=
        pow_le_pow_of_le_one (by linarith [hz.2]) (by linarith [hz.1]) (by omega)
      have hq0 : 0 ≤ (1-z)^(2*(n+1)) := pow_nonneg (by linarith [hz.2]) _
      have hshrink : (1-delta)*(1-z)^(2*(n+1)) ≤ (1-z)^(2*(n+1)) := by
        nlinarith [hd.1]
      linarith
    · refine ⟨1, by norm_num, ?_⟩
      have h0 : (1-(1:ℝ))^(2*1) = 0 := by norm_num
      rw [hz1, h0]
      linarith

end
end FunctionalViability.Robust
