import proofs.G6PDReserve.DriftComparison
import proofs.G6PDReserve.ObservationBounds

namespace G6PDReserve
noncomputable section
open Set

/-- Exact scalar form of positive coefficient kinetics, including g=P. -/
def scalarRate (a b c P g : ℝ) : ℝ :=
  (P-g)/(a*(P-g)+b*g+c)

theorem scalar_den_pos (a b c P g : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hg : 0 ≤ g) (hgP : g ≤ P) :
    0 < a*(P-g)+b*g+c := by
  have := mul_nonneg (le_of_lt ha) (sub_nonneg.mpr hgP)
  have := mul_nonneg (le_of_lt hb) hg
  linarith

theorem scalar_rate_strictAnti (a b c P : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hP : 0 < P) : StrictAntiOn (scalarRate a b c P) (Icc 0 P) := by
  intro x hx y hy hxy
  unfold scalarRate
  apply (div_lt_div_iff₀ (scalar_den_pos a b c P y ha hb hc hy.1 hy.2)
    (scalar_den_pos a b c P x ha hb hc hx.1 hx.2)).mpr
  have h := mul_pos (sub_pos.mpr hxy) (show 0 < b*P+c by positivity)
  nlinarith

/-- A denominator upper certificate yields a target-restricted drift lower bound. -/
theorem scalar_drift_certificate (a b c P R g U q : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hP : 0 < P)
    (hg : g ∈ Icc 0 P) (hR : R ∈ Icc 0 P) (hgR : g ≤ R)
    (hRP : R < P) (hU : (a*(P-R)+b*R+c)/(P-R) ≤ U) :
    1/U-q ≤ scalarRate a b c P g-q := by
  have hden := scalar_den_pos a b c P R ha hb hc hR.1 hR.2
  have hpos : 0 < (a*(P-R)+b*R+c)/(P-R) := div_pos hden (sub_pos.mpr hRP)
  have hbound := one_div_le_one_div_of_le hpos hU
  have hid : 1 / ((a*(P-R)+b*R+c)/(P-R)) = scalarRate a b c P R := by
    simp [scalarRate]
  rw [hid] at hbound
  have hm := (scalar_rate_strictAnti a b c P ha hb hc hP).antitoneOn hg hR hgR
  linarith

theorem positive_drift_reaches (g : ℝ → ℝ) (R m : ℝ)
    (hm : 0 < m) (h0 : g 0 < R)
    (hd : ∀ t ∈ Icc 0 ((R-g 0)/m), HasDerivAt g (deriv g t) t)
    (hbound : ∀ t ∈ Icc 0 ((R-g 0)/m), g t < R → m ≤ deriv g t) :
    ∃ t ∈ Icc (0:ℝ) ((R-g 0)/m), R ≤ g t := by
  let T := (R-g 0)/m
  have hT : 0 ≤ T := le_of_lt (div_pos (sub_pos.mpr h0) hm)
  by_contra hn
  have hbelow : ∀ t ∈ Icc (0:ℝ) T, g t < R := by
    intro t ht
    by_contra h
    exact hn ⟨t,ht,le_of_not_gt h⟩
  have hmono : MonotoneOn (fun t => g t-m*t) (Icc (0:ℝ) T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro t ht
      exact ((hd t ht).sub ((hasDerivAt_id t).const_mul m)).continuousAt.continuousWithinAt
    · intro t ht
      exact ((hd t (interior_subset ht)).sub ((hasDerivAt_id t).const_mul m)).differentiableAt.differentiableWithinAt
    · intro t ht
      have hder : HasDerivAt (fun t => g t-m*t) (deriv g t-m) t := by
        simpa using (hd t (interior_subset ht)).sub ((hasDerivAt_id t).const_mul m)
      rw [hder.deriv]
      have := hbound t (interior_subset ht) (hbelow t (interior_subset ht))
      simpa using sub_nonneg.mpr this
  have h := hmono (show 0 ∈ Icc (0:ℝ) T from ⟨le_rfl,hT⟩)
    (show T ∈ Icc (0:ℝ) T from ⟨hT,le_rfl⟩) hT
  have he : m*T = R-g 0 := by dsimp [T]; field_simp
  have hh := hbelow T ⟨hT,le_rfl⟩
  simp only [mul_zero,sub_zero] at h
  linarith

/-- A strictly decreasing field cannot cross a target whose drift is nonpositive. -/
theorem decreasing_rate_barrier (v g : ℝ → ℝ) (P R q T : ℝ)
    (hT : 0 ≤ T) (hR : R ∈ Icc 0 P) (h0 : g 0 ≤ R)
    (hpool : ∀ t ∈ Icc 0 T, g t ∈ Icc 0 P)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt g (v (g t)-q) t)
    (hv : StrictAntiOn v (Icc 0 P)) (hbad : v R ≤ q) : g T ≤ R := by
  by_contra hn
  have hRT : R < g T := lt_of_not_ge hn
  let B := (R+g T)/2
  have hBR : R < B := by dsimp [B]; linarith
  have hBP : B ≤ P := by have := (hpool T ⟨hT,le_rfl⟩).2; dsimp [B]; linarith
  have hbpool : B ∈ Icc 0 P := ⟨le_trans hR.1 (le_of_lt hBR),hBP⟩
  have hBv : v B < q := lt_of_lt_of_le (hv hR hbpool hBR) hbad
  have hh := image_le_of_deriv_right_lt_deriv_boundary
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (show g 0 ≤ (fun _ : ℝ => B) 0 from le_trans h0 (le_of_lt hBR))
    (fun t => hasDerivAt_const t B)
    (by intro t _ he; rw [he]; linarith :
      ∀ t ∈ Ico 0 T, g t = B → v (g t)-q < 0)
    (show T ∈ Icc (0:ℝ) T from ⟨hT,le_rfl⟩)
  dsimp [B] at hh
  linarith

/-- Equality is excluded too: a finite Lipschitz secant bound leaves an
exponentially positive distance from the target at every finite time. -/
theorem decreasing_rate_no_finite_arrival (v g : ℝ → ℝ) (P R q L T : ℝ)
    (hT : 0 ≤ T) (hR : R ∈ Icc 0 P) (h0 : g 0 < R)
    (hpool : ∀ t ∈ Icc 0 T, g t ∈ Icc 0 P)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt g (v (g t)-q) t)
    (hv : StrictAntiOn v (Icc 0 P)) (hbad : v R ≤ q)
    (hsec : ∀ x ∈ Icc 0 R, v x-v R ≤ L*(R-x)) : g T < R := by
  have hbelow (t : ℝ) (ht : t ∈ Icc 0 T) : g t ≤ R :=
    decreasing_rate_barrier v g P R q t ht.1 hR (le_of_lt h0)
      (fun s hs => hpool s ⟨hs.1,le_trans hs.2 ht.2⟩)
      (fun s hs => hd s ⟨hs.1,le_trans hs.2 ht.2⟩) hv hbad
  have hh := upper_drift_comparison g (fun t => v (g t)-q) L R T hT hd (by
    intro t ht
    have := hsec (g t) ⟨(hpool t ht).1,hbelow t ht⟩
    linarith)
  have he := mul_neg_of_neg_of_pos (sub_neg.mpr h0) (Real.exp_pos (-L*T))
  linarith

theorem scalar_secant_bound (a b c P R x : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hP : 0 < P)
    (hR : R ∈ Icc 0 P) (hx : x ∈ Icc 0 R) :
    scalarRate a b c P x-scalarRate a b c P R ≤ ((b*P+c)/c^2)*(R-x) := by
  have dx := scalar_den_pos a b c P x ha hb hc hx.1 (le_trans hx.2 hR.2)
  have dr := scalar_den_pos a b c P R ha hb hc hR.1 hR.2
  have hdx : c ≤ a*(P-x)+b*x+c := by
    have := mul_nonneg ha.le (sub_nonneg.mpr (le_trans hx.2 hR.2))
    have := mul_nonneg hb.le hx.1
    linarith
  have hdr : c ≤ a*(P-R)+b*R+c := by
    have := mul_nonneg ha.le (sub_nonneg.mpr hR.2)
    have := mul_nonneg hb.le hR.1
    linarith
  have he : scalarRate a b c P x-scalarRate a b c P R =
      ((b*P+c)*(R-x))/((a*(P-x)+b*x+c)*(a*(P-R)+b*R+c)) := by
    unfold scalarRate
    rw [div_sub_div _ _ (ne_of_gt dx) (ne_of_gt dr)]
    congr 1
    ring
  rw [he]
  have hh : c^2 ≤ (a*(P-x)+b*x+c)*(a*(P-R)+b*R+c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdx) (sub_nonneg.mpr hdr)]
  have hnum : 0 ≤ (b*P+c)*(R-x) := mul_nonneg (by positivity) (sub_nonneg.mpr hx.2)
  have hi := div_le_div_of_nonneg_left hnum (sq_pos_of_pos hc) hh
  calc
    _ ≤ ((b*P+c)*(R-x))/c^2 := hi
    _ = _ := by ring

end
end G6PDReserve
