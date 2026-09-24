import proofs.MicrobialFunctionAssay.Certificate

namespace MicrobialFunctionAssay

/-! ## Facet accessors -/

theorem lower_nonneg (q1 q2 B e s J H : ℝ) : 0 ≤ lower q1 q2 B e s J H :=
  le_max_left _ _

theorem lower_ge_first (q1 q2 B e s J H : ℝ) :
    q1 - B ≤ lower q1 q2 B e s J H :=
  le_max_of_le_right (le_max_left _ _)

theorem lower_ge_total (q1 q2 B e s J H : ℝ) :
    q1 + q2 - B - H ≤ lower q1 q2 B e s J H :=
  le_max_of_le_right (le_max_of_le_right (le_max_left _ _))

theorem lower_ge_reserve (q1 q2 B e s J H : ℝ) :
    e*q1 + q2 - e*B - (s-e)*J - H ≤ lower q1 q2 B e s J H :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))

theorem lower_ge_uniform (q1 q2 B e s J H : ℝ) :
    s*q1 + q2 - s*B - H ≤ lower q1 q2 B e s J H :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

/-! ## Maximal explanatory carryover and the remaining-stock form -/

/-- Largest old inventory that can survive recovery when `x` units of credited
material remain after the first collection and at most `J` of them may sit in
the better retained reserve pool. -/
def carry (e s J x : ℝ) : ℝ := e * x + (s - e) * min J x

theorem lower_closed (q1 q2 B e s J H : ℝ)
    (he : 0 ≤ e) (hes : e ≤ s) (hs : s ≤ 1) (hJ : 0 ≤ J) :
    lower q1 q2 B e s J H
      = max 0 (q1 - B) + max 0 (q2 - H - carry e s J (max 0 (B - q1))) := by
  have hs0 : 0 ≤ s := he.trans hes
  have he1 : e ≤ 1 := hes.trans hs
  rcases le_total q1 B with hq | hq
  · have hA : max 0 (q1 - B) = 0 := max_eq_left (by linarith)
    have hx : max 0 (B - q1) = B - q1 := max_eq_right (by linarith)
    rw [hA, hx, zero_add, carry]
    rcases le_total (B - q1) J with hxJ | hxJ
    · rw [min_eq_right hxJ]
      have hrw : q2 - H - (e * (B - q1) + (s - e) * (B - q1))
          = s*q1 + q2 - s*B - H := by ring
      rw [hrw]
      refine le_antisymm ?_ ?_
      · have h1 : (0:ℝ) ≤ max 0 (s*q1 + q2 - s*B - H) := le_max_left _ _
        have h2 : s*q1 + q2 - s*B - H ≤ max 0 (s*q1 + q2 - s*B - H) := le_max_right _ _
        unfold lower
        repeat' apply max_le
        all_goals nlinarith
      · exact max_le (lower_nonneg _ _ _ _ _ _ _) (lower_ge_uniform _ _ _ _ _ _ _)
    · rw [min_eq_left hxJ]
      have hrw : q2 - H - (e * (B - q1) + (s - e) * J)
          = e*q1 + q2 - e*B - (s-e)*J - H := by ring
      rw [hrw]
      refine le_antisymm ?_ ?_
      · have h1 : (0:ℝ) ≤ max 0 (e*q1 + q2 - e*B - (s-e)*J - H) := le_max_left _ _
        have h2 : e*q1 + q2 - e*B - (s-e)*J - H
            ≤ max 0 (e*q1 + q2 - e*B - (s-e)*J - H) := le_max_right _ _
        unfold lower
        repeat' apply max_le
        all_goals nlinarith
      · exact max_le (lower_nonneg _ _ _ _ _ _ _) (lower_ge_reserve _ _ _ _ _ _ _)
  · have hA : max 0 (q1 - B) = q1 - B := max_eq_right (by linarith)
    have hx : max 0 (B - q1) = 0 := max_eq_left (by linarith)
    rw [hA, hx, carry, min_eq_right hJ]
    have hrw : q2 - H - (e * 0 + (s - e) * 0) = q2 - H := by ring
    rw [hrw]
    refine le_antisymm ?_ ?_
    · have h1 : (0:ℝ) ≤ max 0 (q2 - H) := le_max_left _ _
      have h2 : q2 - H ≤ max 0 (q2 - H) := le_max_right _ _
      unfold lower
      repeat' apply max_le
      all_goals nlinarith
    · rcases le_total (q2 - H) 0 with h | h
      · rw [max_eq_left h]
        have := lower_ge_first q1 q2 B e s J H
        linarith
      · rw [max_eq_right h]
        have := lower_ge_total q1 q2 B e s J H
        linarith

/-! ## Attainment: the certificate is exactly the minimum of the source class -/

theorem attain_aux (q1 q2 B e s J H R0 A x r p U T F2 V : ℝ)
    (hA : A = max 0 (q1 - B)) (hx : x = max 0 (B - q1))
    (hr : r = min J x) (hp : p = x - r)
    (hU : U = max 0 (R0 + A - r)) (hT : T = max 0 (r - R0 - A))
    (hF2 : F2 = max 0 (q2 - H - (e*p + s*r))) (hV : V = max 0 (q2 - e*p))
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hH : 0 ≤ H)
    (he : 0 ≤ e) (hes : e ≤ s) (hs : s ≤ 1)
    (hR0 : 0 ≤ R0) (hR0B : R0 ≤ B) :
    ∃ h : History,
      h.e = e ∧ h.s = s ∧
      h.first.p0 = B - R0 ∧ h.first.r0 = R0 ∧
      h.first.p0 + h.first.r0 ≤ B ∧
      h.first.collect = q1 ∧ h.second.collect = q2 ∧
      h.first.r ≤ J ∧
      h.first.uptake ≤ max 0 (min J B - R0) ∧
      h.inputP + h.inputR ≤ H ∧
      h.first.fresh + h.second.fresh = lower q1 q2 B e s J H := by
  have hs0 : 0 ≤ s := he.trans hes
  have he1 : e ≤ 1 := hes.trans hs
  have hA0 : 0 ≤ A := by rw [hA]; exact le_max_left _ _
  have hx0 : 0 ≤ x := by rw [hx]; exact le_max_left _ _
  have hxB : x ≤ B := by rw [hx]; exact max_le hB (by linarith)
  have hAx : A - x = q1 - B := by
    rcases le_total q1 B with h | h
    · rw [hA, hx, max_eq_left (by linarith : q1 - B ≤ 0),
        max_eq_right (by linarith : (0:ℝ) ≤ B - q1)]; ring
    · rw [hA, hx, max_eq_right (by linarith : (0:ℝ) ≤ q1 - B),
        max_eq_left (by linarith : B - q1 ≤ 0)]; ring
  have hr0 : 0 ≤ r := by rw [hr]; exact le_min hJ hx0
  have hrJ : r ≤ J := by rw [hr]; exact min_le_left _ _
  have hrx : r ≤ x := by rw [hr]; exact min_le_right _ _
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  have hU0 : 0 ≤ U := by rw [hU]; exact le_max_left _ _
  have hT0 : 0 ≤ T := by rw [hT]; exact le_max_left _ _
  have hUT : U - T = R0 + A - r := by
    rcases le_total 0 (R0 + A - r) with h | h
    · rw [hU, hT, max_eq_right h, max_eq_left (by linarith : r - R0 - A ≤ 0)]; ring
    · rw [hU, hT, max_eq_left h, max_eq_right (by linarith : (0:ℝ) ≤ r - R0 - A)]; ring
  have hUle : U ≤ R0 + A := by rw [hU]; exact max_le (by linarith) (by linarith)
  have hep : 0 ≤ e*p := mul_nonneg he hp0
  have hsr : 0 ≤ s*r := mul_nonneg hs0 hr0
  have hF20 : 0 ≤ F2 := by rw [hF2]; exact le_max_left _ _
  have hF2f : q2 - H - (e*p + s*r) ≤ F2 := by rw [hF2]; exact le_max_right _ _
  have hV0 : 0 ≤ V := by rw [hV]; exact le_max_left _ _
  have hVf : q2 - e*p ≤ V := by rw [hV]; exact le_max_right _ _
  have hVub : V ≤ s*r + H + F2 := by
    rw [hV]; exact max_le (by linarith) (by linarith)
  have hfp : B - R0 + U - T - q1 - 0 = p := by rw [hp]; linarith
  have hfr : R0 + A + T - U - 0 = r := by linarith
  refine ⟨{
    first := {
      p0 := B - R0, r0 := R0, fresh := A, release := U, uptake := T,
      collect := q1, lossP := 0, lossR := 0,
      nonneg := ⟨by linarith, hR0, hA0, hU0, hT0, hq1, le_refl 0, le_refl 0⟩,
      enoughR := by linarith,
      enoughP := by linarith,
      release_available := by linarith }
    second := {
      p0 := e*p, r0 := s*r + H, fresh := F2, release := V, uptake := 0,
      collect := q2, lossP := e*p + V - q2, lossR := s*r + H + F2 - V,
      nonneg := ⟨hep, by linarith, hF20, hV0, le_refl 0, hq2, by linarith, by linarith⟩,
      enoughR := by linarith,
      enoughP := by linarith,
      release_available := by linarith }
    e := e
    s := s
    inputP := 0
    inputR := H
    fractions := ⟨he, hes, hs⟩
    inputs_nonneg := ⟨le_refl 0, hH⟩
    p_recovery := by
      show e*p ≤ e * (B - R0 + U - T - q1 - 0) + 0
      rw [hfp]; linarith
    r_recovery := by
      show s*r + H ≤ s * (R0 + A + T - U - 0) + H
      rw [hfr] }, rfl, rfl, rfl, rfl, by linarith, rfl, rfl, ?_, ?_, by linarith, ?_⟩
  · show R0 + A + T - U - 0 ≤ J
    rw [hfr]; exact hrJ
  · show T ≤ max 0 (min J B - R0)
    rw [hT]
    exact max_le (le_max_left _ _)
      ((by linarith [le_min hrJ (hrx.trans hxB)] : r - R0 - A ≤ min J B - R0).trans
        (le_max_right _ _))
  · show A + F2 = lower q1 q2 B e s J H
    rw [lower_closed q1 q2 B e s J H he hes hs hJ]
    simp only [carry]
    rw [← hx, ← hr, ← hA]
    have hcong : q2 - H - (e*p + s*r) = q2 - H - (e * x + (s - e) * r) := by
      rw [hp]; ring
    rw [hF2, hcong]

theorem lower_attained (q1 q2 B e s J H R0 : ℝ)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hH : 0 ≤ H)
    (he : 0 ≤ e) (hes : e ≤ s) (hs : s ≤ 1)
    (hR0 : 0 ≤ R0) (hR0B : R0 ≤ B) :
    ∃ h : History,
      h.e = e ∧ h.s = s ∧
      h.first.p0 = B - R0 ∧ h.first.r0 = R0 ∧
      h.first.p0 + h.first.r0 ≤ B ∧
      h.first.collect = q1 ∧ h.second.collect = q2 ∧
      h.first.r ≤ J ∧
      h.first.uptake ≤ max 0 (min J B - R0) ∧
      h.inputP + h.inputR ≤ H ∧
      h.first.fresh + h.second.fresh = lower q1 q2 B e s J H :=
  attain_aux q1 q2 B e s J H R0 _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl
    hq1 hq2 hB hJ hH he hes hs hR0 hR0B

/-- Exact minimum: the certificate is sound and attained, so no strictly larger
lower bound is valid under the same calibration data. -/
theorem lower_is_minimum (q1 q2 B e s J H : ℝ)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hH : 0 ≤ H)
    (he : 0 ≤ e) (hes : e ≤ s) (hs : s ≤ 1) :
    IsLeast {z : ℝ | ∃ h : History, h.e = e ∧ h.s = s ∧
        h.first.p0 + h.first.r0 ≤ B ∧ q1 ≤ h.first.collect ∧
        q2 ≤ h.second.collect ∧ h.first.r ≤ J ∧
        h.inputP + h.inputR ≤ H ∧ z = h.first.fresh + h.second.fresh}
      (lower q1 q2 B e s J H) := by
  constructor
  · obtain ⟨h, he', hs', -, -, hB', hc1, hc2, hrJ, -, hin, hfresh⟩ :=
      lower_attained q1 q2 B e s J H 0 hq1 hq2 hB hJ hH he hes hs le_rfl hB
    exact ⟨h, he', hs', hB', le_of_eq hc1.symm, le_of_eq hc2.symm, hrJ, hin, hfresh.symm⟩
  · rintro z ⟨h, he', hs', hB', hc1, hc2, hrJ, hin, rfl⟩
    have := observed_source_bound h q1 q2 B J H hc1 hc2 hB' hrJ hin
    rwa [he', hs'] at this

/-! ## Bounded uptake in place of a direct pre-wash reserve measurement -/

theorem lower_sound_uptake (q1 q2 B e s J H f1 f2 p r : ℝ)
    (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (he : 0 ≤ e) (hes : e ≤ s) (hs : s ≤ 1)
    (h1 : q1 + p + r ≤ B + f1) (h2 : q2 ≤ e*p + s*r + H + f2)
    (hj : r ≤ J + f1) : lower q1 q2 B e s J H ≤ f1 + f2 := by
  have hs0 : 0 ≤ s := he.trans hes
  have he1 : e ≤ 1 := hes.trans hs
  have ep : e*p ≤ p := mul_le_of_le_one_left hp he1
  have sr : s*r ≤ r := mul_le_of_le_one_left hr hs
  have ep' : e*p ≤ s*p := mul_le_mul_of_nonneg_right hes hp
  have ef : e*f1 ≤ f1 := mul_le_of_le_one_left hf1 he1
  have sf : s*f1 ≤ f1 := mul_le_of_le_one_left hf1 hs
  have ee := mul_le_mul_of_nonneg_left h1 he
  have ss := mul_le_mul_of_nonneg_left h1 hs0
  have jj := mul_le_mul_of_nonneg_left hj (sub_nonneg.mpr hes)
  unfold lower
  repeat' apply max_le
  all_goals nlinarith

/-- Reserve ceiling implied by an initial reserve bound and a cumulative
first-window uptake bound. The conclusion is `r ≤ J₀ + F₁`, not `r ≤ J₀`. -/
theorem prewash_reserve_from_uptake (w : Window) (Rbar Tbar : ℝ)
    (hR : w.r0 ≤ Rbar) (hT : w.uptake ≤ Tbar) :
    w.r ≤ (Rbar + Tbar) + w.fresh := by
  have hn := w.nonneg
  unfold Window.r
  linarith [hn.2.2.2.1, hn.2.2.2.2.2.2.2]

theorem uptake_source_bound (h : History) (q1 q2 B Rbar Tbar H : ℝ)
    (hobs1 : q1 ≤ h.first.collect) (hobs2 : q2 ≤ h.second.collect)
    (hB : h.first.p0 + h.first.r0 ≤ B)
    (hR : h.first.r0 ≤ Rbar) (hT : h.first.uptake ≤ Tbar)
    (hH : h.inputP + h.inputR ≤ H) :
    lower q1 q2 B h.e h.s (Rbar + Tbar) H ≤ h.first.fresh + h.second.fresh := by
  apply lower_sound_uptake (p := h.first.p) (r := h.first.r)
  · exact h.first.nonneg.2.2.1
  · exact h.second.nonneg.2.2.1
  · exact (pool_nonneg h.first).1
  · exact (pool_nonneg h.first).2
  · exact h.fractions.1
  · exact h.fractions.2.1
  · exact h.fractions.2.2
  · linarith [source_account h.first]
  · linarith [recovery_account h]
  · exact prewash_reserve_from_uptake h.first Rbar Tbar hR hT

/-- The same expression is also exactly attained in the uptake-bounded class,
so the substitution `J := Rbar + Tbar` loses nothing. -/
theorem uptake_bound_attained (q1 q2 B e s H Rbar Tbar : ℝ)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hRbar : 0 ≤ Rbar) (hTbar : 0 ≤ Tbar)
    (he : 0 ≤ e) (hes : e ≤ s) (hs : s ≤ 1) :
    ∃ h : History,
      h.e = e ∧ h.s = s ∧
      h.first.p0 + h.first.r0 ≤ B ∧
      h.first.collect = q1 ∧ h.second.collect = q2 ∧
      h.first.r0 ≤ Rbar ∧ h.first.uptake ≤ Tbar ∧
      h.inputP + h.inputR ≤ H ∧
      h.first.fresh + h.second.fresh = lower q1 q2 B e s (Rbar + Tbar) H := by
  obtain ⟨h, he', hs', -, hr0, hB', hc1, hc2, -, hup, hin, hfresh⟩ :=
    lower_attained q1 q2 B e s (Rbar + Tbar) H (min Rbar B) hq1 hq2 hB
      (by linarith) hH he hes hs (le_min hRbar hB) (min_le_right _ _)
  refine ⟨h, he', hs', hB', hc1, hc2, ?_, ?_, hin, hfresh⟩
  · rw [hr0]; exact min_le_left _ _
  · refine hup.trans (max_le hTbar ?_)
    rcases le_total Rbar B with hc | hc
    · rw [min_eq_left hc]
      exact sub_le_iff_le_add.mpr (by linarith [min_le_left (Rbar + Tbar) B])
    · rw [min_eq_right hc]
      exact sub_le_iff_le_add.mpr (by linarith [min_le_right (Rbar + Tbar) B])

end MicrobialFunctionAssay
