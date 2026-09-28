import proofs.DStabilityHardness.Attainable
import proofs.DStabilityHardness.Main

/-!
# Exact classification of all partitions on the Pell core family (restricted coNP-completeness)

For `ρ ∈ [17/10, 7/4]`, a port self-coefficient `h₀` and positive loads `r` of total `G` whose load
points `[h₀ - G, h₀]` lie within `1/2` of the window centre `h_v(ρ)`, and with both endpoints outside
the window: the star matrix `attached (coreB ρ h₀) port r` is D-stable iff no subset-sum load point
`h₀ - Σ_S r` lies in the open window `{Kf ρ · < 0}`; otherwise it is strictly D-unstable.

A subset `S` with `Kf ρ (h₀ - Σ_S r) < 0` is therefore a polynomial-size certificate of instability,
and subset-sum dynamic programming decides D-stability in pseudo-polynomial time on this class.
-/

namespace DStabilityHardness

open DUnstableCores CollectiveInstability DStabilityCharacterization.Granularity
open DStabilityCharacterization.SpectralContinuation
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- On the imaginary axis the height `|ω| α` of a piece is its semicircle height. -/
theorem axis_semi (z : ℂ) (hz : z.re = 0) (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    |z.im| * lagShift z r t = semi (staticLoad z r t) r := by
  have hsq := axis_lag_sq z hz r t
  have hlag : 0 ≤ lagShift z r t := (shift_pos hz.ge hr ht).le
  unfold semi
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hlag]

set_option maxHeartbeats 1000000 in
/-- **No imaginary-axis eigenvalue** when no subset-sum load point lies in the window. -/
theorem no_axis_window [Nonempty κ] (ρ h₀ : ℝ) (hρ0 : 17 / 10 ≤ ρ) (hρ1 : ρ ≤ 7 / 4)
    (r : κ → ℝ) (hr : ∀ j, 0 < r j) (hbox0 : 3 ≤ h₀ - ∑ j, r j) (hbox1 : h₀ ≤ 5)
    (hsub : ∀ S : Finset κ, 0 ≤ Kf ρ (h₀ - ∑ j ∈ S, r j))
    (d : Fin 4 ⊕ κ → ℝ) (hd : ∀ i, 0 < d i) (z : ℂ) (u : Fin 4 ⊕ κ → ℂ)
    (hu : HasEigenpair (rightScale (attached (coreB ρ h₀) port r) d) z u) : z.re ≠ 0 := by
  intro hz
  obtain ⟨hn, hc, hl⟩ := attached_pencil _ _ _ d hd z u hu
  let qi : Fin 4 → ℝ := fun i => (d (.inl i))⁻¹
  let t : κ → ℝ := fun j => (d (.inr j))⁻¹
  have hqi : ∀ i, 0 < qi i := fun i => inv_pos.mpr (hd _)
  have ht : ∀ j, 0 < t j := fun j => inv_pos.mpr (hd _)
  obtain ⟨hv0, hst⟩ := attached_static (coreB ρ h₀) port r qi t hqi ht z hz.ge _ _ hn hc hl
  set v : Fin 4 → ℂ := fun i => (d (.inl i) : ℂ) * u (.inl i)
  set X : ℝ := ∑ k, staticLoad z (r k) (t k) with hXdef
  set a : ℝ := ∑ k, lagShift z (r k) (t k) with hadef
  have hX0 : 0 < X := Finset.sum_pos (fun j _ => (axis_load_bounds z hz (r j) (t j) (hr j)).1)
    Finset.univ_nonempty
  have hXG : X ≤ ∑ j, r j := Finset.sum_le_sum (fun j _ => (axis_load_bounds z hz (r j) (t j) (hr j)).2)
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun j _ => (shift_pos hz.ge (hr j) (ht j)).le)
  let q' : Fin 4 → ℝ := fun i => qi i + if i = port then a else 0
  have hq' : ∀ i, 0 < q' i := by
    intro i; dsimp only [q']; split_ifs <;> linarith [hqi i]
  set h := h₀ - X with hhdef
  have hb : InBox ρ h := ⟨hρ0, hρ1, by linarith, by linarith⟩
  have he' : ∀ i, ∑ j, (coreB ρ h i j : ℂ) * v j = z * (q' i : ℂ) * v i := by
    intro i; rw [hhdef, ← loadCore_coreB]; exact hst i
  have heig := eigenpair_of_pencil (coreB ρ h) q' hq' z v hv0 he'
  have hd' : ∀ i, 0 < (fun i => (q' i)⁻¹) i := fun i => inv_pos.mpr (hq' i)
  by_cases hz0 : z = 0
  · rw [vec4_eta (fun i => (q' i)⁻¹)] at heig
    have hqz := quartic_of_eigenpair (scaled_charpoly ρ h _ _ _ _) heig
    rw [hz0] at hqz
    simp [quartic] at hqz
    obtain ⟨-, -, -, c4p⟩ := coeffs_pos hb (hd' 0) (hd' 1) (hd' 2) (hd' 3)
    exact absurd hqz (ne_of_gt c4p)
  have hω : z.im ≠ 0 := fun h0 => hz0 (Complex.ext (by simp [hz]) (by simp [h0]))
  have hzI : z = (z.im : ℂ) * Complex.I := Complex.ext (by simp [hz]) (by simp)
  by_cases hK : 0 ≤ Kf ρ h
  · have := static_dStable hb hK _ hd' z _ heig
    linarith
  push Not at hK
  rw [hzI] at heig
  have hcb := contact_bound hb _ hd' z.im hω _ heig
  have hk := k2_pos hρ0 hρ1
  have e : (z.im / (fun i => (q' i)⁻¹) 3) = z.im * q' port := by simp [div_inv_eq_mul]
  rw [e] at hcb
  -- window in load coordinates: centre c = h₀ - h_v, squared half-width W
  set c := h₀ - hv ρ with hcdef
  have hKw : ∀ y, Kf ρ (h₀ - y) = k2 ρ * ((y - c) ^ 2 - Wd ρ) := by
    intro y; rw [Kf_window ρ _ hk, hcdef]; ring
  have hWpos : 0 < Wd ρ := by
    rw [hKw] at hK
    by_contra hc'; push Not at hc'
    have := mul_nonneg hk.le (by nlinarith [sq_nonneg (X - c)] : 0 ≤ (X - c) ^ 2 - Wd ρ)
    linarith
  set w := Real.sqrt (Wd ρ) with hwdef
  have hw2 : w ^ 2 = Wd ρ := Real.sq_sqrt hWpos.le
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  -- no subset sum in (c - w, c + w)
  have hgap : ∀ S : Finset κ, ¬ (c - w < ∑ j ∈ S, r j ∧ ∑ j ∈ S, r j < c + w) := by
    intro S ⟨h1, h2⟩
    have hs := hsub S
    rw [hKw] at hs
    have hlt : (∑ j ∈ S, r j - c) ^ 2 < w ^ 2 := by
      have : |∑ j ∈ S, r j - c| < w := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
      calc (∑ j ∈ S, r j - c) ^ 2 = |∑ j ∈ S, r j - c| ^ 2 := (sq_abs _).symm
        _ < w ^ 2 := pow_lt_pow_left₀ this (abs_nonneg _) two_ne_zero
    rw [hw2] at hlt
    have := mul_neg_of_pos_of_neg hk (by linarith : (∑ j ∈ S, r j - c) ^ 2 - Wd ρ < 0)
    linarith
  have hXwin : (X - c) ^ 2 < w ^ 2 := by
    rw [hKw] at hK; rw [hw2]
    by_contra hc'; push Not at hc'
    have := mul_nonneg hk.le (sub_nonneg.mpr hc')
    linarith
  have hXin : c - w < X ∧ X < c + w := by
    have := abs_lt_of_sq_lt_sq hXwin hw0
    constructor <;> linarith [abs_lt.mp this]
  -- attainable-region inequality
  have hxr : ∀ j, 0 ≤ staticLoad z (r j) (t j) ∧ staticLoad z (r j) (t j) ≤ r j := fun j =>
    ⟨(axis_load_bounds z hz (r j) (t j) (hr j)).1.le, (axis_load_bounds z hz (r j) (t j) (hr j)).2⟩
  have hatt := attainable r hr (c - w) (c + w) hgap _ (fun j => staticLoad z (r j) (t j)) rfl hxr
    hXin.1 hXin.2
  have hsemi : ∑ j, semi (staticLoad z (r j) (t j)) (r j) = |z.im| * a := by
    rw [hadef, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => (axis_semi z hz (r j) (t j) (hr j) (ht j)).symm)
  rw [hsemi] at hatt
  -- contact bound in load coordinates
  have hcon : (z.im * q' port) ^ 2 ≤ (X - (c - w)) * ((c + w) - X) := by
    have hK' := hKw X
    have e2 : h = h₀ - X := hhdef
    rw [← e2] at hK'
    rw [hK'] at hcb
    have e3 : (X - (c - w)) * ((c + w) - X) = Wd ρ - (X - c) ^ 2 := by rw [← hw2]; ring
    rw [e3]
    have h2 : k2 ρ * (z.im * q' port) ^ 2 ≤ k2 ρ * (Wd ρ - (X - c) ^ 2) := by linarith
    exact le_of_mul_le_mul_left h2 hk
  have hq3 : q' port = qi port + a := by simp [q']
  have hωpos : 0 < z.im ^ 2 := by positivity
  have hqa : a ^ 2 < (qi port + a) ^ 2 := by nlinarith [hqi port, ha0]
  have hfin : z.im ^ 2 * a ^ 2 < z.im ^ 2 * (qi port + a) ^ 2 := mul_lt_mul_of_pos_left hqa hωpos
  have hsqA : (|z.im| * a) ^ 2 = z.im ^ 2 * a ^ 2 := by rw [mul_pow, sq_abs]
  rw [hq3, mul_pow] at hcon
  linarith

/-- `W` is nondecreasing in `ρ` on `[√3, 7/4]`. -/
theorem Wd_mono {ρ ρ₁ : ℝ} (h0 : 17 / 10 ≤ ρ) (h1 : ρ ≤ ρ₁) (h1' : ρ₁ ≤ 7 / 4) (h3 : 3 ≤ ρ ^ 2) :
    Wd ρ ≤ Wd ρ₁ := by
  have hk := k2_pos h0 (le_trans h1 h1')
  have hk1 := k2_pos (le_trans h0 h1) h1'
  have hWd : ∀ y, 0 < k2 y → Wd y = 36 / 25 * ((2 / 5 + gam y) / k2 y) ^ 2 * (y ^ 2 - 3) := by
    intro y hy; unfold Wd; rw [disc_factor]; field_simp; ring
  rw [hWd ρ hk, hWd ρ₁ hk1]
  have hR0 : 0 ≤ (2 / 5 + gam ρ) / k2 ρ := div_nonneg (by unfold gam; linarith) hk.le
  have hR : (2 / 5 + gam ρ) / k2 ρ ≤ (2 / 5 + gam ρ₁) / k2 ρ₁ := by
    rw [div_le_div_iff₀ hk hk1]
    have hg : 2 / 5 + gam ρ ≤ 2 / 5 + gam ρ₁ := by unfold gam; linarith
    have hkk : k2 ρ₁ ≤ k2 ρ := by unfold k2; nlinarith
    have hg0 : 0 ≤ 2 / 5 + gam ρ := by unfold gam; linarith
    nlinarith [mul_le_mul hg hkk hk1.le (by unfold gam; linarith : (0:ℝ) ≤ 2 / 5 + gam ρ₁)]
  have hsq : ((2 / 5 + gam ρ) / k2 ρ) ^ 2 ≤ ((2 / 5 + gam ρ₁) / k2 ρ₁) ^ 2 :=
    pow_le_pow_left₀ hR0 hR 2
  have hρρ : ρ ^ 2 - 3 ≤ ρ₁ ^ 2 - 3 := by nlinarith
  have hA : 0 ≤ ρ ^ 2 - 3 := by linarith
  have := mul_le_mul hsq hρρ hA (sq_nonneg _)
  nlinarith

omit [Fintype κ] in
theorem path_continuousOn' (ρ₁ h₀ : ℝ) (hρ1 : ρ₁ ≤ 7 / 4) (r : κ → ℝ) (d : Fin 4 ⊕ κ → ℝ) :
    ContinuousOn (fun ρ => rightScale (attached (coreB ρ (h₀ - hv ρ₁ + hv ρ)) port r) d)
      (Set.Icc (17 / 10) ρ₁) := by
  have hhv := hv_continuousOn ρ₁ hρ1
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  simp only [rightScale]
  apply ContinuousOn.mul _ continuousOn_const
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [attached, coreB, gam] <;> fun_prop
  · exact continuousOn_const
  · exact continuousOn_const
  · exact continuousOn_const

/-- **Classification, stable side.** -/
theorem classification_stable [Nonempty κ] (ρ₁ h₀ : ℝ) (hρ10 : 17 / 10 ≤ ρ₁) (hρ1 : ρ₁ ≤ 7 / 4)
    (r : κ → ℝ) (hr : ∀ j, 0 < r j)
    (hlo : hv ρ₁ - 1 / 2 ≤ h₀ - ∑ j, r j) (hhi : h₀ ≤ hv ρ₁ + 1 / 2)
    (hsub : ∀ S : Finset κ, 0 ≤ Kf ρ₁ (h₀ - ∑ j ∈ S, r j)) :
    DStable (attached (coreB ρ₁ h₀) port r) := by
  set o := h₀ - hv ρ₁ with hodef
  set G := ∑ j, r j with hGdef
  have hG0 : 0 < G := Finset.sum_pos (fun j _ => hr j) Finset.univ_nonempty
  -- relative position of every subset sum
  have hk1 := k2_pos hρ10 hρ1
  have hrel : ∀ S : Finset κ, Wd ρ₁ ≤ (o - ∑ j ∈ S, r j) ^ 2 := by
    intro S
    have hs := hsub S
    rw [Kf_window ρ₁ _ hk1] at hs
    have e : h₀ - ∑ j ∈ S, r j - hv ρ₁ = o - ∑ j ∈ S, r j := by rw [hodef]; ring
    rw [e] at hs
    by_contra hc; push Not at hc
    have := mul_neg_of_pos_of_neg hk1 (by linarith : (o - ∑ j ∈ S, r j) ^ 2 - Wd ρ₁ < 0)
    linarith
  -- hypotheses along the path
  have hpath_sub : ∀ ρ ∈ Set.Icc (17 / 10 : ℝ) ρ₁, ∀ S : Finset κ,
      0 ≤ Kf ρ (h₀ - hv ρ₁ + hv ρ - ∑ j ∈ S, r j) := by
    intro ρ hρ S
    have hk := k2_pos hρ.1 (le_trans hρ.2 hρ1)
    rw [Kf_window ρ _ hk]
    have e : h₀ - hv ρ₁ + hv ρ - ∑ j ∈ S, r j - hv ρ = o - ∑ j ∈ S, r j := by rw [hodef]; ring
    rw [e]
    apply mul_nonneg hk.le
    rcases lt_or_ge (ρ ^ 2) 3 with h3 | h3
    · have : Wd ρ < 0 := by
        unfold Wd; rw [disc_factor]
        apply div_neg_of_neg_of_pos _ (by positivity)
        have : 0 < 2 / 5 + gam ρ := by unfold gam; linarith [hρ.1]
        have h3' : ρ ^ 2 - 3 < 0 := by linarith
        exact mul_neg_of_pos_of_neg (by positivity) h3'
      nlinarith [sq_nonneg (o - ∑ j ∈ S, r j)]
    · linarith [Wd_mono hρ.1 hρ.2 hρ1 h3, hrel S]
  have hpath_box : ∀ ρ ∈ Set.Icc (17 / 10 : ℝ) ρ₁,
      3 ≤ h₀ - hv ρ₁ + hv ρ - G ∧ h₀ - hv ρ₁ + hv ρ ≤ 5 := by
    intro ρ hρ
    obtain ⟨b0, b1⟩ := hv_bounds hρ.1 (le_trans hρ.2 hρ1)
    constructor <;> linarith
  -- base point: no window at ρ = 17/10
  have hW0 : Wd (17 / 10) < 0 := by
    unfold Wd; rw [disc_factor]
    apply div_neg_of_neg_of_pos _ (by
      have := k2_pos (le_refl (17 / 10 : ℝ)) (by norm_num); positivity)
    have : 0 < 2 / 5 + gam (17 / 10) := by unfold gam; norm_num
    nlinarith [this]
  have hbase : DStable (attached (coreB (17 / 10) (h₀ - hv ρ₁ + hv (17 / 10))) port r) := by
    obtain ⟨b0, b1⟩ := hpath_box (17 / 10) ⟨le_rfl, hρ10⟩
    have hk0 := k2_pos (le_refl (17 / 10 : ℝ)) (by norm_num)
    have hstat : ∀ x : ℝ, 0 ≤ x → x ≤ G →
        DStable (loadCore (coreB (17 / 10) (h₀ - hv ρ₁ + hv (17 / 10))) port x) := by
      intro x hx0 hx1
      rw [loadCore_coreB]
      have hb : InBox (17 / 10) (h₀ - hv ρ₁ + hv (17 / 10) - x) :=
        ⟨le_rfl, by norm_num, by linarith, by linarith⟩
      apply static_dStable hb
      rw [Kf_window _ _ hk0]
      apply mul_nonneg hk0.le
      nlinarith [sq_nonneg (h₀ - hv ρ₁ + hv (17 / 10) - x - hv (17 / 10))]
    apply attached_dStable_of_det _ _ r hr
    · intro x hx0 hx1; exact hstat x hx0.le hx1.le
    · exact det_ne_zero_of_dStable _ (hstat G hG0.le le_rfl)
  intro d hd
  have hpath := hurwitzStable_on_preconnected (Set.Icc (17 / 10) ρ₁) isPreconnected_Icc
    (fun ρ => rightScale (attached (coreB ρ (h₀ - hv ρ₁ + hv ρ)) port r) d)
    (path_continuousOn' ρ₁ h₀ hρ1 r d)
    (by
      intro ρ hρ z v hv
      obtain ⟨b0, b1⟩ := hpath_box ρ hρ
      exact no_axis_window ρ _ hρ.1 (le_trans hρ.2 hρ1) r hr b0 b1 (hpath_sub ρ hρ) d hd z v hv)
    (17 / 10) ⟨le_rfl, hρ10⟩ (hbase d hd)
  have := hpath ρ₁ ⟨hρ10, le_rfl⟩
  simpa using this

/-- **Classification, unstable side.** A nonempty proper subset whose load point lies in the window
yields a strictly destabilizing scaling. -/
theorem classification_unstable (ρ₁ h₀ : ℝ) (hρ10 : 17 / 10 ≤ ρ₁) (hρ1 : ρ₁ ≤ 7 / 4)
    (r : κ → ℝ) (hr : ∀ j, 0 < r j)
    (hlo : hv ρ₁ - 1 / 2 ≤ h₀ - ∑ j, r j) (hhi : h₀ ≤ hv ρ₁ + 1 / 2)
    (S : Finset κ) (hS0 : 0 < ∑ j ∈ S, r j) (hS1 : ∑ j ∈ S, r j < ∑ j, r j)
    (hK : Kf ρ₁ (h₀ - ∑ j ∈ S, r j) < 0) :
    DUnstable (attached (coreB ρ₁ h₀) port r) := by
  obtain ⟨b0, b1⟩ := hv_bounds hρ10 hρ1
  have hb : InBox ρ₁ (h₀ - ∑ j ∈ S, r j) := ⟨hρ10, hρ1, by linarith, by linarith⟩
  have hun := static_dUnstable hb hK
  rw [← loadCore_coreB] at hun
  rcases hun with ⟨d, hd, z, u, hz, hu⟩
  let qq : Fin 4 → ℝ := fun i => (d i)⁻¹
  let v : Fin 4 → ℂ := fun i => (d i : ℂ) * u i
  have hdn (i : Fin 4) : (d i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd i))
  have hqq : ∀ i, 0 < qq i := fun i => inv_pos.mpr (hd i)
  have hv0 : v ≠ 0 := by
    intro h; apply hu.1; funext i
    exact (mul_eq_zero.mp (congrFun h i)).resolve_left (hdn i)
  have he : ∀ i, ∑ j, (loadCore (coreB ρ₁ h₀) port (∑ j ∈ S, r j) i j : ℂ) * v j
      = z * (qq i : ℂ) * v i := by
    intro i
    have hi := hu.2 i
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Complex.ofReal_mul] at hi
    have heq : z * (qq i : ℂ) * v i = z * u i := by
      dsimp [qq, v]; push_cast; field_simp [hdn i]
    rw [heq]
    simpa [v, mul_assoc] using hi
  obtain ⟨t, ht, hload, hshift⟩ := subset_realization z hz (∑ j, r j) (∑ j ∈ S, r j) (qq port)
    hS0 hS1 (hqq port) r hr rfl S rfl
  exact reverse_absorption _ port r t ht qq hqq z hz _ v hv0 he hload hshift

/-- **Exact classification (restricted coNP-completeness).** On the Pell core family with load points
within `1/2` of the window centre and both endpoints outside the window, the star matrix is D-stable
iff no subset-sum load point lies in the window, and strictly D-unstable otherwise. -/
theorem classification [Nonempty κ] (ρ₁ h₀ : ℝ) (hρ10 : 17 / 10 ≤ ρ₁) (hρ1 : ρ₁ ≤ 7 / 4)
    (r : κ → ℝ) (hr : ∀ j, 0 < r j)
    (hlo : hv ρ₁ - 1 / 2 ≤ h₀ - ∑ j, r j) (hhi : h₀ ≤ hv ρ₁ + 1 / 2)
    (hend0 : 0 ≤ Kf ρ₁ h₀) (hend1 : 0 ≤ Kf ρ₁ (h₀ - ∑ j, r j)) :
    (DStable (attached (coreB ρ₁ h₀) port r) ↔ ∀ S : Finset κ, 0 ≤ Kf ρ₁ (h₀ - ∑ j ∈ S, r j)) ∧
    ((∃ S : Finset κ, Kf ρ₁ (h₀ - ∑ j ∈ S, r j) < 0) → DUnstable (attached (coreB ρ₁ h₀) port r)) := by
  have hunst : (∃ S : Finset κ, Kf ρ₁ (h₀ - ∑ j ∈ S, r j) < 0) →
      DUnstable (attached (coreB ρ₁ h₀) port r) := by
    rintro ⟨S, hS⟩
    have hS0 : 0 < ∑ j ∈ S, r j := by
      rcases S.eq_empty_or_nonempty with h | h
      · rw [h, Finset.sum_empty, sub_zero] at hS; linarith
      · exact Finset.sum_pos (fun j _ => hr j) h
    have hS1 : ∑ j ∈ S, r j < ∑ j, r j := by
      by_contra hc; push Not at hc
      have hle : ∑ j ∈ S, r j ≤ ∑ j, r j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun j _ _ => (hr j).le)
      have heq : ∑ j ∈ S, r j = ∑ j, r j := le_antisymm hle hc
      rw [heq] at hS; linarith
    exact classification_unstable ρ₁ h₀ hρ10 hρ1 r hr hlo hhi S hS0 hS1 hS
  refine ⟨⟨fun hst S => ?_, classification_stable ρ₁ h₀ hρ10 hρ1 r hr hlo hhi⟩, hunst⟩
  by_contra hc; push Not at hc
  obtain ⟨d, hd, z, u, hz, hu⟩ := hunst ⟨S, hc⟩
  have := hst d hd z u hu
  linarith

end

end DStabilityHardness
