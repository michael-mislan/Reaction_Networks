import proofs.MixedDegradation.TypeVReduced

namespace MixedDegradation.TypeV

/-- Action of a logarithmically scaled derivative row. -/
def TangentRow (b c d h k r s t : ℝ) : ℝ :=
  b * (s + t - r) + c * (s - r) + d * (t - r) + h * t + k * s

theorem tangent_min_zero {b c d h k r s t : ℝ}
    (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hrs : r ≤ s) (hrt : r ≤ t) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hz : TangentRow b c d h k r s t = 0) : r = 0 ∧ s = 0 ∧ t = 0 := by
  have h1 := mul_nonneg hc (sub_nonneg.mpr hrs)
  have h2 := mul_nonneg hd (sub_nonneg.mpr hrt)
  have h3 := mul_nonneg hh ht
  have h4 := mul_nonneg hk hs
  have hsum : s + t - r ≤ 0 := by
    unfold TangentRow at hz
    have hm : b * (s + t - r) ≤ 0 := by
      linarith only [hz, h1, h2, h3, h4]
    by_contra hn
    exact (not_lt_of_ge hm) (mul_pos hb (lt_of_not_ge hn))
  exact ⟨by linarith, by linarith, by linarith⟩

theorem tangent_max_zero {b c d h k r s t : ℝ}
    (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hsr : s ≤ r) (htr : t ≤ r) (hs : s ≤ 0) (ht : t ≤ 0)
    (hz : TangentRow b c d h k r s t = 0) : r = 0 ∧ s = 0 ∧ t = 0 := by
  have hn : TangentRow b c d h k (-r) (-s) (-t) = 0 := by
    unfold TangentRow at hz ⊢
    linarith only [hz]
  obtain ⟨hr, hs', ht'⟩ := tangent_min_zero hb hc hd hh hk
    (neg_le_neg hsr) (neg_le_neg htr) (neg_nonneg.mpr hs) (neg_nonneg.mpr ht) hn
  exact ⟨by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 1200000 in
/-- The median-sign mechanism is uniform in all nonnegative leakage coefficients. -/
theorem tangent_kernel_zero (p : ReducedParams) (z : Fin 3 → ℝ)
    (hz : ∀ i, TangentRow (p.b i) (p.c i) (p.d i) (p.h i) (p.k i)
      (z i) (z (i+1)) (z (i+2)) = 0) : z = 0 := by
  have hmin (i : Fin 3) := tangent_min_zero (p.b_pos i) (p.c_nonneg i)
    (p.d_nonneg i) (p.h_nonneg i) (p.k_nonneg i) (r := z i)
    (s := z (i+1)) (t := z (i+2))
  have hmax (i : Fin 3) := tangent_max_zero (p.b_pos i) (p.c_nonneg i)
    (p.d_nonneg i) (p.h_nonneg i) (p.k_nonneg i) (r := z i)
    (s := z (i+1)) (t := z (i+2))
  have hall : z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 := by
    have h0 := hz 0
    have h1 := hz 1
    have h2 := hz 2
    have mn0 := hmin 0
    have mn1 := hmin 1
    have mn2 := hmin 2
    have mx0 := hmax 0
    have mx1 := hmax 1
    have mx2 := hmax 2
    change TangentRow (p.b 0) (p.c 0) (p.d 0) (p.h 0) (p.k 0) (z 0) (z 1) (z 2) = 0 at h0
    change TangentRow (p.b 1) (p.c 1) (p.d 1) (p.h 1) (p.k 1) (z 1) (z 2) (z 0) = 0 at h1
    change TangentRow (p.b 2) (p.c 2) (p.d 2) (p.h 2) (p.k 2) (z 2) (z 0) (z 1) = 0 at h2
    have a0 : z 0 ≤ z 1 → z 0 ≤ z 2 → 0 ≤ z 1 → 0 ≤ z 2 →
        z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 := fun a b c d => mn0 a b c d h0
    have a1 : z 1 ≤ z 2 → z 1 ≤ z 0 → 0 ≤ z 2 → 0 ≤ z 0 →
        z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 := by
      intro a b c d
      obtain ⟨r,s,t⟩ := mn1 a b c d h1
      exact ⟨t,r,s⟩
    have a2 : z 2 ≤ z 0 → z 2 ≤ z 1 → 0 ≤ z 0 → 0 ≤ z 1 →
        z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 := by
      intro a b c d
      obtain ⟨r,s,t⟩ := mn2 a b c d h2
      exact ⟨s,t,r⟩
    have b0 : z 1 ≤ z 0 → z 2 ≤ z 0 → z 1 ≤ 0 → z 2 ≤ 0 →
        z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 := fun a b c d => mx0 a b c d h0
    have b1 : z 2 ≤ z 1 → z 0 ≤ z 1 → z 2 ≤ 0 → z 0 ≤ 0 →
        z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 := by
      intro a b c d
      obtain ⟨r,s,t⟩ := mx1 a b c d h1
      exact ⟨t,r,s⟩
    have b2 : z 0 ≤ z 2 → z 1 ≤ z 2 → z 0 ≤ 0 → z 1 ≤ 0 →
        z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 := by
      intro a b c d
      obtain ⟨r,s,t⟩ := mx2 a b c d h2
      exact ⟨s,t,r⟩
    rcases le_total (z 0) (z 1) with h01 | h10 <;>
      rcases le_total (z 1) (z 2) with h12 | h21 <;>
      rcases le_total (z 0) (z 2) with h02 | h20 <;>
      by_cases hs0 : 0 ≤ z 0 <;> by_cases hs1 : 0 ≤ z 1 <;>
      by_cases hs2 : 0 ≤ z 2 <;>
      first
      | solve | apply a0 <;> linarith
      | solve | apply a1 <;> linarith
      | solve | apply a2 <;> linarith
      | solve | apply b0 <;> linarith
      | solve | apply b1 <;> linarith
      | solve | apply b2 <;> linarith
  funext i
  fin_cases i <;> simp_all

end MixedDegradation.TypeV
