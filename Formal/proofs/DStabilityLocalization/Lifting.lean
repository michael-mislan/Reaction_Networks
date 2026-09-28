import proofs.DStabilityLocalization.LiftingAnalytic

/-!
# Lifting (node N6, Theorem 5.1)

Strict growth of any boundary system gives strict growth of the star: fast pieces get inverse
rate `ε`, slow pieces `1/ε`, the pieces of each synchronized group the group's inverse rate.
The reduced determinants `g_ε` converge to the boundary system's as `ε → 0` uniformly near the
unstable root, and Hurwitz's theorem (`hurwitz_zero`) produces a root of `g_ε` in the open right
half-plane.  Loads of either sign; any number of channels.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Matrix Complex Set Filter Topology Metric
open scoped BigOperators

namespace DStabilityLocalization
open DUnstableCores

variable {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype C] [DecidableEq C]

/-- Frequency response of a piece in the lifting family (`ε = 0` is the boundary system). -/
def liftPhi (σ : Role) (tD ε : ℝ) (z : ℂ) : ℂ :=
  if σ = Role.F then 1 / (1 + z * ε) else if σ = Role.D then 1 / (1 + z * tD) else
    ε / (ε + z)

def liftVal (ch : κ → C) (r : κ → ℝ) (σ : κ → Role) (tg : C → ℝ) (ε : ℝ) (z : ℂ) (c : C) :
    ℂ :=
  ∑ p, if ch p = c then (r p : ℂ) * liftPhi (σ p) (tg (ch p)) ε z else 0

/-- Inverse rates of the lifting family at `ε > 0`. -/
def liftRate (ch : κ → C) (σ : κ → Role) (tg : C → ℝ) (ε : ℝ) (p : κ) : ℝ :=
  if σ p = Role.F then ε else if σ p = Role.D then tg (ch p) else ε⁻¹

theorem liftRate_pos (ch : κ → C) (σ : κ → Role) (tg : C → ℝ) (htg : ∀ c, 0 < tg c)
    (ε : ℝ) (hε : 0 < ε) (p : κ) : 0 < liftRate ch σ tg ε p := by
  unfold liftRate
  split_ifs
  · exact hε
  · exact htg _
  · exact inv_pos.mpr hε

theorem re_pos_den {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 ≤ t) : 1 + z * (t : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  nlinarith [mul_nonneg hz.le ht]

theorem liftVal_pos (ch : κ → C) (r : κ → ℝ) (σ : κ → Role) (tg : C → ℝ) (ε : ℝ)
    (hε : 0 < ε) (z : ℂ) (hz : 0 < z.re) :
    liftVal ch r σ tg ε z = lagValue ch r (liftRate ch σ tg ε) z := by
  funext c
  unfold liftVal lagValue
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs with hc
  · unfold liftPhi liftRate
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have hden : (ε : ℂ) + z ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    by_cases hF : σ p = Role.F
    · simp [hF, div_eq_mul_inv]
    · by_cases hD : σ p = Role.D
      · simp [hF, hD, div_eq_mul_inv]
      · simp only [hF, hD, if_false, reduceCtorEq]
        push_cast
        field_simp
  · rfl

theorem liftVal_zero (ch : κ → C) (r : κ → ℝ) (σ : κ → Role) (tg : C → ℝ) (z : ℂ) (c : C) :
    liftVal ch r σ tg 0 z c =
      (∑ p, if ch p = c then (if σ p = Role.F then (r p : ℂ) else 0) else 0) +
        (bdLoad ch r σ c : ℂ) / (1 + z * (tg c : ℂ)) := by
  unfold liftVal bdLoad
  push_cast
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hc : ch p = c
  · subst hc
    unfold liftPhi
    by_cases hF : σ p = Role.F
    · simp [hF]
    · by_cases hD : σ p = Role.D
      · simp [hF, hD]; ring
      · simp [hF, hD]
  · simp [hc]

/-- At `ε = 0` the lifting pencil is the boundary system's reduced pencil. -/
theorem pencil_lift_zero (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (σ : κ → Role) (q : ι → ℝ) (tg : C → ℝ) (z : ℂ) :
    pencil B u v q (liftVal ch r σ tg 0 z) z =
      pencil (bdCore B u v ch r σ) u v q (lagValue id (bdLoad ch r σ) tg z) z := by
  have hlag : ∀ c, lagValue id (bdLoad ch r σ) tg z c =
      (bdLoad ch r σ c : ℂ) / (1 + z * (tg c : ℂ)) := by
    intro c
    show (∑ p : C, if p = c then (bdLoad ch r σ p : ℂ) / (1 + z * (tg p : ℂ)) else 0) = _
    rw [Fintype.sum_eq_single c (fun x hx => if_neg hx), if_pos rfl]
  ext i j
  simp only [pencil, bdCore]
  push_cast
  simp_rw [hlag, liftVal_zero, add_mul]
  rw [Finset.sum_add_distrib]
  have hF : (∑ c, (∑ p, if ch p = c then (if σ p = Role.F then (r p : ℂ) else 0) else 0) *
      (u c i : ℂ) * (v c j : ℂ)) =
      ∑ p, if σ p = Role.F then (r p : ℂ) * (u (ch p) i : ℂ) * (v (ch p) j : ℂ) else 0 := by
    have := sum_channel_regroup ch (fun p => if σ p = Role.F then (r p : ℂ) else 0)
      (fun c => (u c i : ℂ) * (v c j : ℂ))
    simp only [mul_assoc] at this ⊢
    rw [this]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  rw [hF]
  have hcast : (∑ p, ((if σ p = Role.F then r p * u (ch p) i * v (ch p) j else 0 : ℝ) : ℂ)) =
      ∑ p, if σ p = Role.F then (r p : ℂ) * (u (ch p) i : ℂ) * (v (ch p) j : ℂ) else 0 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  rw [← hcast]
  ring

theorem norm_liftPhi_le (σ : Role) {tD ε : ℝ} (htD : 0 < tD) (hε : 0 ≤ ε) {z : ℂ}
    (hz : 0 < z.re) : ‖liftPhi σ tD ε z‖ ≤ 1 := by
  have key : ∀ t : ℝ, 0 ≤ t → ‖(1 : ℂ) / (1 + z * t)‖ ≤ 1 := by
    intro t ht
    rw [norm_div, norm_one, div_le_one (norm_pos_iff.mpr (re_pos_den hz ht))]
    have := Complex.re_le_norm (1 + z * (t : ℂ))
    simp at this
    nlinarith [mul_nonneg hz.le ht]
  unfold liftPhi
  split_ifs
  · exact key ε hε
  · exact key tD htD.le
  · rcases hε.eq_or_lt with h0 | hpos
    · subst h0; simp
    · have hden : (ε : ℂ) + z ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      rw [norm_div, div_le_one (norm_pos_iff.mpr hden), Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hpos]
      have := Complex.re_le_norm ((ε : ℂ) + z)
      simp at this
      linarith

theorem norm_liftVal_le (ch : κ → C) (r : κ → ℝ) (σ : κ → Role) {tg : C → ℝ}
    (htg : ∀ c, 0 < tg c) {ε : ℝ} (hε : 0 ≤ ε) {z : ℂ} (hz : 0 < z.re) (c : C) :
    ‖liftVal ch r σ tg ε z c‖ ≤ ∑ p, |r p| := by
  unfold liftVal
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_liftPhi_le _ (htg _) hε hz)
  · simp

/-- Levy–Desplanques at a large complex frequency. -/
theorem pencil_det_ne_of_norm (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (q : ι → ℝ)
    (hq : ∀ i, 0 < q i) (K : ℝ) (hK : 0 ≤ K) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z : ℂ, R₀ ≤ ‖z‖ → ∀ ℓ : C → ℂ, (∀ c, ‖ℓ c‖ ≤ K) →
      (pencil B u v q ℓ z).det ≠ 0 := by
  let R : ι → ℝ := fun i => ∑ j, (|B i j| + K * ∑ c, |u c i| * |v c j|)
  have hR : ∀ i, 0 ≤ R i := fun i => Finset.sum_nonneg (fun j _ =>
    add_nonneg (abs_nonneg _) (mul_nonneg hK (Finset.sum_nonneg (fun c _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
  have hS : 0 ≤ ∑ i, R i / q i :=
    Finset.sum_nonneg (fun i _ => div_nonneg (hR i) (hq i).le)
  refine ⟨1 + ∑ i, R i / q i, by linarith, ?_⟩
  intro z hz ℓ hℓ
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  set E : ι → ℂ := fun j => (B i j : ℂ) + ∑ c, ℓ c * u c i * v c j with hE
  have hEb : ∀ j, ‖E j‖ ≤ |B i j| + K * ∑ c, |u c i| * |v c j| := by
    intro j
    refine (norm_add_le _ _).trans (add_le_add (by simp) ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun c _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have := hℓ c
    have h0 : 0 ≤ |u c i| * |v c j| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [norm_nonneg (ℓ c)]
  have hsumE : ∑ j, ‖E j‖ ≤ R i := Finset.sum_le_sum (fun j _ => hEb j)
  have hRi : R i / q i ≤ ∑ i, R i / q i :=
    Finset.single_le_sum (f := fun i => R i / q i) (fun i _ => div_nonneg (hR i) (hq i).le)
      (Finset.mem_univ i)
  have hzq : R i < ‖z‖ * q i := by
    have h1 : R i / q i < ‖z‖ := by linarith
    rwa [div_lt_iff₀ (hq i)] at h1
  have hent : ∀ j, pencil B u v q ℓ z i j = (if i = j then z * (q i : ℂ) else 0) - E j := by
    intro j; simp only [pencil, hE]; ring
  have hdiag : ‖pencil B u v q ℓ z i i‖ ≥ ‖z‖ * q i - ‖E i‖ := by
    rw [hent i, if_pos rfl]
    have h1 := norm_sub_norm_le (z * (q i : ℂ)) (E i)
    have h2 : ‖z * (q i : ℂ)‖ = ‖z‖ * q i := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq i)]
    linarith
  have hoff : ∑ j ∈ Finset.univ.erase i, ‖pencil B u v q ℓ z i j‖ =
      ∑ j ∈ Finset.univ.erase i, ‖E j‖ := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hent j, if_neg (Ne.symm (Finset.ne_of_mem_erase hj)), zero_sub, norm_neg]
  rw [hoff]
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => ‖E j‖) (Finset.mem_univ i)
  linarith

theorem continuousOn_liftPhi (σ : Role) (tD : ℝ) (htD : 0 < tD) (S : Set (ℝ × ℂ))
    (hS : ∀ x ∈ S, 0 ≤ x.1 ∧ 0 < x.2.re) :
    ContinuousOn (fun x : ℝ × ℂ => liftPhi σ tD x.1 x.2) S := by
  unfold liftPhi
  by_cases hF : σ = Role.F
  · simp only [hF, if_true]
    refine ContinuousOn.div continuousOn_const (by fun_prop) (fun x hx => ?_)
    exact re_pos_den (hS x hx).2 (hS x hx).1
  · by_cases hD : σ = Role.D
    · simp only [hF, hD, if_true, if_false, reduceCtorEq]
      exact ContinuousOn.div continuousOn_const (by fun_prop)
        (fun x hx => re_pos_den (hS x hx).2 htD.le)
    · simp only [hF, hD, if_false]
      refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun x hx => ?_)
      intro h; have := congrArg Complex.re h; simp at this
      linarith [(hS x hx).1, (hS x hx).2]

theorem differentiableAt_liftPhi (σ : Role) (tD : ℝ) (htD : 0 < tD) (ε : ℝ) (hε : 0 ≤ ε)
    (z : ℂ) (hz : 0 < z.re) : DifferentiableAt ℂ (fun w => liftPhi σ tD ε w) z := by
  unfold liftPhi
  by_cases hF : σ = Role.F
  · simp only [hF, if_true]
    exact (differentiableAt_const _).div (by fun_prop) (re_pos_den hz hε)
  · by_cases hD : σ = Role.D
    · simp only [hF, hD, if_true, if_false, reduceCtorEq]
      exact (differentiableAt_const _).div (by fun_prop) (re_pos_den hz htD.le)
    · simp only [hF, hD, if_false]
      refine (differentiableAt_const _).div (by fun_prop) ?_
      intro h; have := congrArg Complex.re h; simp at this; linarith

/-- Entries of the lifting pencil are holomorphic in the right half-plane. -/
theorem differentiableAt_lift_entry (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C)
    (r : κ → ℝ) (σ : κ → Role) (q : ι → ℝ) (tg : C → ℝ) (htg : ∀ c, 0 < tg c) (ε : ℝ)
    (hε : 0 ≤ ε) (z : ℂ) (hz : 0 < z.re) (i j : ι) :
    DifferentiableAt ℂ (fun w => pencil B u v q (liftVal ch r σ tg ε w) w i j) z := by
  simp only [pencil, liftVal]
  have hφ : ∀ p, DifferentiableAt ℂ (fun w => liftPhi (σ p) (tg (ch p)) ε w) z :=
    fun p => differentiableAt_liftPhi _ _ (htg _) ε hε z hz
  refine DifferentiableAt.sub (DifferentiableAt.sub ?_ (differentiableAt_const _)) ?_
  · by_cases hij : i = j
    · simp only [hij, if_true]; fun_prop
    · simp only [hij, if_false]; exact differentiableAt_const _
  · refine DifferentiableAt.fun_sum (fun c _ => ?_)
    refine DifferentiableAt.mul_const (DifferentiableAt.mul_const ?_ _) _
    refine DifferentiableAt.fun_sum (fun p _ => ?_)
    by_cases hc : ch p = c
    · simp only [if_pos hc]; exact (hφ p).const_mul _
    · simp only [hc, if_false]; exact differentiableAt_const _

/-- Entries of the lifting pencil are jointly continuous in `(ε, z)`. -/
theorem continuousOn_lift_entry (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C)
    (r : κ → ℝ) (σ : κ → Role) (q : ι → ℝ) (tg : C → ℝ) (htg : ∀ c, 0 < tg c)
    (S : Set (ℝ × ℂ)) (hS : ∀ x ∈ S, 0 ≤ x.1 ∧ 0 < x.2.re) (i j : ι) :
    ContinuousOn (fun x : ℝ × ℂ => pencil B u v q (liftVal ch r σ tg x.1 x.2) x.2 i j) S := by
  simp only [pencil, liftVal]
  have hφ : ∀ p, ContinuousOn (fun x : ℝ × ℂ => liftPhi (σ p) (tg (ch p)) x.1 x.2) S :=
    fun p => continuousOn_liftPhi _ _ (htg _) S hS
  refine ContinuousOn.sub (ContinuousOn.sub ?_ continuousOn_const) ?_
  · by_cases hij : i = j
    · simp only [hij, if_true]; exact (by fun_prop : Continuous _).continuousOn
    · simp only [hij, if_false]; exact continuousOn_const
  · refine continuousOn_finsetSum _ (fun c _ => ?_)
    refine ContinuousOn.mul (ContinuousOn.mul ?_ continuousOn_const) continuousOn_const
    refine continuousOn_finsetSum _ (fun p _ => ?_)
    by_cases hc : ch p = c
    · simp only [if_pos hc]; exact continuousOn_const.mul (hφ p)
    · simp only [hc, if_false]; exact continuousOn_const

/-- **Lifting (Theorem 5.1).** Strict growth of a boundary system gives strict growth of the
star. -/
theorem dUnstable_of_boundary (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (σ : κ → Role) (h : DUnstable (bdSystem B u v ch r σ)) : DUnstable (star B u v ch r) := by
  obtain ⟨d', hd', z₀, y, hre, hy⟩ := h
  set q : ι → ℝ := fun i => (d' (.inl i))⁻¹ with hqdef
  set tg : C → ℝ := fun c => (d' (.inr c))⁻¹ with htgdef
  have hq : ∀ i, 0 < q i := fun i => inv_pos.mpr (hd' _)
  have htg : ∀ c, 0 < tg c := fun c => inv_pos.mpr (hd' _)
  have hz1 : ∀ c, 1 + z₀ * (((d' (.inr c))⁻¹ : ℝ) : ℂ) ≠ 0 :=
    fun c => re_pos_den hre (htg c).le
  obtain ⟨x, hx, hker⟩ := pencil_kernel_of_eigenpair (bdCore B u v ch r σ) u v id
    (bdLoad ch r σ) d' hd' z₀ y hy hz1
  let G : ℝ → ℂ → ℂ := fun ε z => (pencil B u v q (liftVal ch r σ tg ε z) z).det
  have hG0 : G 0 z₀ = 0 := by
    simp only [G]
    rw [pencil_lift_zero]
    exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hker⟩
  have hdiffG : ∀ ε, 0 ≤ ε → ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (G ε) z :=
    fun ε hε z hz => differentiableAt_det _ z
      (fun i j => differentiableAt_lift_entry B u v ch r σ q tg htg ε hε z hz i j)
  -- a point of the right half-plane where `G 0` does not vanish
  have hK : 0 ≤ ∑ p, |r p| := Finset.sum_nonneg (fun p _ => abs_nonneg _)
  obtain ⟨R₀, hR₀, hR⟩ := pencil_det_ne_of_norm B u v q hq _ hK
  have hz₁ : G 0 (R₀ : ℂ) ≠ 0 := by
    have hre1 : 0 < ((R₀ : ℂ)).re := by simpa using hR₀
    refine hR (R₀ : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR₀]) _ ?_
    exact fun c => norm_liftVal_le ch r σ htg (le_refl 0) hre1 c
  -- isolated zeros of `G 0` in the right half-plane
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hdiffU : DifferentiableOn ℂ (G 0) {z : ℂ | 0 < z.re} :=
    fun z hz => (hdiffG 0 (le_refl _) z hz).differentiableWithinAt
  obtain ⟨ρ, hρ, hρR, hsph⟩ := exists_sphere_ne hU hUc hdiffU (show z₀ ∈ {z : ℂ | 0 < z.re}
    from hre) (show (R₀ : ℂ) ∈ {z : ℂ | 0 < z.re} by simpa using hR₀) hz₁ (z₀.re / 2)
    (by linarith)
  -- the closed ball lies in the right half-plane
  have hball : ∀ z ∈ closedBall z₀ ρ, z₀.re / 2 < z.re := by
    intro z hz
    have h1 : dist z z₀ ≤ ρ := hz
    rw [dist_eq_norm] at h1
    have h2 := Complex.abs_re_le_norm (z - z₀)
    rw [Complex.sub_re] at h2
    have h3 := neg_abs_le (z.re - z₀.re)
    linarith
  have hS : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ closedBall z₀ ρ, 0 ≤ x.1 ∧ 0 < x.2.re := by
    rintro ⟨ε, z⟩ ⟨hε, hz⟩
    exact ⟨hε.1, by linarith [hball z hz]⟩
  have hcont : ContinuousOn (fun x : ℝ × ℂ => G x.1 x.2) (Icc (0 : ℝ) 1 ×ˢ closedBall z₀ ρ) :=
    continuousOn_det _ _ (fun i j => continuousOn_lift_entry B u v ch r σ q tg htg _ hS i j)
  have hdiff : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ z ∈ closedBall z₀ ρ, DifferentiableAt ℂ (G ε) z :=
    fun ε hε z hz => hdiffG ε hε.1 z (by linarith [hball z hz])
  obtain ⟨ε, ⟨hε0, hε1⟩, z₂, hz₂, hG⟩ := hurwitz_zero hρ hcont hdiff hG0 hsph
  have hre2 : 0 < z₂.re := by linarith [hball z₂ hz₂]
  -- back to an eigenpair of the star
  simp only [G] at hG
  rw [liftVal_pos ch r σ tg ε hε0 z₂ hre2] at hG
  obtain ⟨x₂, hx₂, hker₂⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hG
  have hrate := liftRate_pos ch σ tg htg ε hε0
  obtain ⟨y₂, hy₂⟩ := eigenpair_of_pencil_kernel B u v ch r q (liftRate ch σ tg ε) hq hrate z₂
    (fun p => re_pos_den hre2 (hrate p).le) x₂ hx₂ hker₂
  refine ⟨_, ?_, z₂, y₂, hre2, hy₂⟩
  intro a
  rcases a with i | p
  · exact inv_pos.mpr (hq i)
  · exact inv_pos.mpr (hrate p)

end DStabilityLocalization
