import proofs.DStability5x5.MorseCoverage

/-!
# Bounded time-scale stability (Theorem A4)

For `κ ≥ 1` let `K_κ = {d > 0 : d i ≤ κ d j for all i, j}` be the cone of positive rate vectors
whose pairwise ratios are at most `κ`.  A real matrix `A` is *`κ`-stable* (`KStable κ A`) if
`A · diag d` is Hurwitz for every `d ∈ K_κ`.

* `kStable_iff_no_cone_contact`: `KStable κ A ↔ A Hurwitz ∧ no contact in K_κ`
  (Johnson's criterion restricted to the cone; continuation on the convex cone).
* The homogeneous contact form `homContact A (e, ω) = det (iω·1 - A·diag e)` turns contacts in
  `K_κ` into zeros on the compact box `[1, κ]ⁿ × (0, W]` (`exists_box_of_cone_contact`).
* `kStable_iff_no_boxFaceCritical` (Theorem A4): for every C¹ function `φ`,
  `KStable κ A ↔ A Hurwitz ∧ no Fritz-John point of φ on the zero set of homContact, taken on the
  face of the box that contains it`.  The minimizer of `φ` over the compact zero set lies in the
  relative interior of a unique face; there it is an equality-constrained Fritz-John point, whose
  multiplier functional vanishes on the face directions.
* `dStable_iff_forall_kStable`: D-stability is `κ`-stability for every `κ`.
-/

noncomputable section

open Matrix Filter Topology Set

namespace DStability5x5

open DUnstableCores DStabilityCharacterization.SpectralContinuation

variable {n : ℕ}

/-- The cone `K_κ` of positive rate vectors with all pairwise ratios at most `κ`. -/
def InCone (κ : ℝ) (d : Fin n → ℝ) : Prop := (∀ i, 0 < d i) ∧ ∀ i j, d i ≤ κ * d j

/-- `κ`-bounded D-stability: `A · diag d` is Hurwitz for every `d ∈ K_κ`. -/
def KStable (κ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ d, InCone κ d → HurwitzStable (rightScale A d)

theorem inCone_smul {κ c : ℝ} {d : Fin n → ℝ} (hd : InCone κ d) (hc : 0 < c) :
    InCone κ (fun i => c * d i) := by
  refine ⟨fun i => mul_pos hc (hd.1 i), fun i j => ?_⟩
  calc c * d i ≤ c * (κ * d j) := mul_le_mul_of_nonneg_left (hd.2 i j) hc.le
    _ = κ * (c * d j) := by ring

theorem convex_inCone (κ : ℝ) : Convex ℝ {d : Fin n → ℝ | InCone κ d} := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hx1 := hx.1 i
    have hy1 := hy.1 i
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      subst hb1
      rw [← ha0]
      simpa using hy1
    · have h1 := mul_pos hapos hx1
      have h2 := mul_nonneg hb hy1.le
      linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hx.2 i j) ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2 i j) hb
    calc a * x i + b * y i ≤ a * (κ * x j) + b * (κ * y j) := add_le_add h1 h2
      _ = κ * (a * x j + b * y j) := by ring

/-- An imaginary-axis eigenvalue at a scaling in `K_κ` yields a contact in `K_κ`. -/
theorem cone_contact_of_axis (A : Matrix (Fin n) (Fin n) ℝ) (hA : HurwitzStable A) {κ : ℝ}
    {d : Fin n → ℝ} (hd : InCone κ d) (z : ℂ) (v : Fin n → ℂ)
    (hv : HasEigenpair (rightScale A d) z v) (hz : z.re = 0) :
    ∃ d', InCone κ d' ∧ contactDet A d' = 0 := by
  have key : ∀ (z : ℂ) (v : Fin n → ℂ), HasEigenpair (rightScale A d) z v → z.re = 0 →
      0 < z.im → ∃ d', InCone κ d' ∧ contactDet A d' = 0 := by
    intro z v hv hz him
    refine ⟨fun i => (z.im)⁻¹ * d i, inCone_smul hd (inv_pos.mpr him), ?_⟩
    rw [contact_iff_eigenpair]
    refine ⟨v, ?_⟩
    have h := eigenpair_rescale A d (z.im)⁻¹ z v hv
    have hz' : (((z.im)⁻¹ : ℝ) : ℂ) * z = Complex.I := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hz, Complex.I_re]
        ring
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hz, Complex.I_im]
        field_simp
        norm_num
    rw [hz'] at h
    exact h
  rcases lt_trichotomy z.im 0 with him | him | him
  · have hc := eigenpair_conj _ z v hv
    exact key (starRingEnd ℂ z) _ hc (by simpa using hz) (by simpa using him)
  · exfalso
    have hz0 : z = 0 := Complex.ext hz him
    subst hz0
    exact no_zero_eigen_of_hurwitz A hA d hd.1 v hv
  · exact key z v hv hz him

/-- **Johnson's criterion on the cone `K_κ`.** -/
theorem kStable_iff_no_cone_contact {κ : ℝ} (hκ : 1 ≤ κ) (A : Matrix (Fin n) (Fin n) ℝ) :
    KStable κ A ↔ HurwitzStable A ∧ ¬ ∃ d, InCone κ d ∧ contactDet A d = 0 := by
  have h1 : InCone κ (fun _ : Fin n => (1 : ℝ)) :=
    ⟨fun _ => one_pos, fun _ _ => by simpa using hκ⟩
  constructor
  · intro hK
    refine ⟨by simpa using hK _ h1, ?_⟩
    rintro ⟨d, hd, hc⟩
    obtain ⟨v, hv⟩ := (contact_iff_eigenpair A d).mp hc
    have h := hK d hd Complex.I v hv
    simp at h
  · rintro ⟨hH, hno⟩ d hd
    have hbase : HurwitzStable (rightScale A (fun _ => (1 : ℝ))) := by simpa using hH
    have hcont : ContinuousOn (fun d : Fin n → ℝ => rightScale A d) {d | InCone κ d} := by
      apply Continuous.continuousOn
      change Continuous (fun d : Fin n → ℝ => fun i j => A i j * d j)
      fun_prop
    refine hurwitzStable_on_preconnected {d : Fin n → ℝ | InCone κ d}
      (convex_inCone κ).isPreconnected (fun d => rightScale A d) hcont ?_
      (fun _ => 1) h1 hbase d hd
    intro t ht z v hv hz
    exact hno (cone_contact_of_axis A hH ht z v hv hz)

theorem kStable_mono {κ κ' : ℝ} (h : κ ≤ κ') {A : Matrix (Fin n) (Fin n) ℝ}
    (hK : KStable κ' A) : KStable κ A := by
  intro d hd
  refine hK d ⟨hd.1, fun i j => ?_⟩
  calc d i ≤ κ * d j := hd.2 i j
    _ ≤ κ' * d j := mul_le_mul_of_nonneg_right h (hd.1 j).le

/-- **D-stability is `κ`-stability for every `κ`.** -/
theorem dStable_iff_forall_kStable (A : Matrix (Fin n) (Fin n) ℝ) :
    DStable A ↔ ∀ κ : ℝ, 1 ≤ κ → KStable κ A := by
  constructor
  · intro hA κ _ d hd
    exact hA d hd.1
  · intro hK d hd
    let κ : ℝ := 1 + ∑ i, ∑ j, d i / d j
    have hterm : ∀ i j, d i / d j ≤ ∑ i, ∑ j, d i / d j := by
      intro i j
      have hnn : ∀ i j, 0 ≤ d i / d j := fun i j => div_nonneg (hd i).le (hd j).le
      calc d i / d j ≤ ∑ j, d i / d j :=
            Finset.single_le_sum (f := fun j => d i / d j) (fun j _ => hnn i j)
              (Finset.mem_univ j)
        _ ≤ ∑ i, ∑ j, d i / d j :=
            Finset.single_le_sum (f := fun i => ∑ j, d i / d j)
              (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) (Finset.mem_univ i)
    have hsum_nn : 0 ≤ ∑ i, ∑ j, d i / d j :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        div_nonneg (hd i).le (hd j).le
    have hκ : 1 ≤ κ := by simp only [κ]; linarith
    refine hK κ hκ d ⟨hd, fun i j => ?_⟩
    have h1 : d i / d j ≤ κ := by simp only [κ]; linarith [hterm i j]
    exact (div_le_iff₀ (hd j)).mp h1

/-- **Johnson's criterion.** A real matrix is D-stable iff it is Hurwitz and has no positive contact. -/
theorem dStable_iff_no_contact (A : Matrix (Fin n) (Fin n) ℝ) :
    DStable A ↔ HurwitzStable A ∧ ¬ ∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧ contactDet A d = 0 := by
  constructor
  · intro hA
    have hK := (dStable_iff_forall_kStable A).mp hA
    refine ⟨((kStable_iff_no_cone_contact (le_refl 1) A).mp (hK 1 (le_refl 1))).1, ?_⟩
    rintro ⟨d, hd, hc⟩
    obtain ⟨v, hv⟩ := (contact_iff_eigenpair A d).mp hc
    have h := hA d hd Complex.I v hv
    simp at h
  · rintro ⟨hH, hno⟩
    apply (dStable_iff_forall_kStable A).mpr
    intro κ hκ
    exact (kStable_iff_no_cone_contact hκ A).mpr ⟨hH, fun ⟨d, hd, hc⟩ => hno ⟨d, hd.1, hc⟩⟩

/-! ## The homogeneous contact form and the compact box -/

/-- Homogeneous contact form `G(e, ω) = det (iω·1 - A·diag e)`. -/
def homContact (A : Matrix (Fin n) (Fin n) ℝ) (x : (Fin n → ℝ) × ℝ) : ℂ :=
  (((x.2 : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) -
    complexify (rightScale A x.1)).det

theorem homContact_eq_zero_iff (A : Matrix (Fin n) (Fin n) ℝ) (x : (Fin n → ℝ) × ℝ) :
    homContact A x = 0 ↔ ∃ v, HasEigenpair (rightScale A x.1) ((x.2 : ℂ) * Complex.I) v := by
  unfold homContact
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v, hv0, fun i => ?_⟩
    have := congrFun hv i
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linear_combination -this
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v, hv0, funext fun i => ?_⟩
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [hv i]
    ring

theorem homContact_eq_zero_iff_contact (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ)
    {ω : ℝ} (hω : 0 < ω) :
    homContact A (e, ω) = 0 ↔ contactDet A (fun i => ω⁻¹ * e i) = 0 := by
  have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  rw [homContact_eq_zero_iff, contact_iff_eigenpair]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    have h := eigenpair_rescale A e ω⁻¹ _ v hv
    have hI : ((ω⁻¹ : ℝ) : ℂ) * ((ω : ℂ) * Complex.I) = Complex.I := by
      push_cast
      rw [← mul_assoc, inv_mul_cancel₀ hω', one_mul]
    rw [hI] at h
    exact h
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    have h := eigenpair_rescale A (fun i => ω⁻¹ * e i) ω _ v hv
    have he : (fun i => ω * (ω⁻¹ * e i)) = e := by
      funext i
      rw [← mul_assoc, mul_inv_cancel₀ hω.ne', one_mul]
    rw [he] at h
    exact h

theorem homContact_contDiff (A : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ 1 (homContact A) := by
  unfold homContact
  simp_rw [Matrix.det_apply]
  apply ContDiff.sum
  intro σ _
  simp only [Units.smul_def, zsmul_eq_mul]
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  simp only [Matrix.sub_apply, Matrix.smul_apply, complexify, rightScale, smul_eq_mul]
  apply ContDiff.sub
  · have h : ContDiff ℝ 1 (fun x : (Fin n → ℝ) × ℝ => ((x.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_snd
    exact (h.mul contDiff_const).mul contDiff_const
  · have h : ContDiff ℝ 1 (fun x : (Fin n → ℝ) × ℝ => A (σ i) i * x.1 i) :=
      contDiff_const.mul ((contDiff_apply ℝ ℝ i).comp contDiff_fst)
    exact Complex.ofRealCLM.contDiff.comp h

theorem continuous_homContact_joint :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × ℝ) => homContact p.1 p.2) := by
  unfold homContact
  apply Continuous.matrix_det
  change Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × ℝ) =>
    fun i j => ((p.2.2 : ℂ) * Complex.I) * (1 : Matrix (Fin n) (Fin n) ℂ) i j -
      ((p.1 i j * p.2.1 j : ℝ) : ℂ))
  fun_prop

/-- The box `[1, κ]ⁿ`. -/
def InBox (κ : ℝ) (e : Fin n → ℝ) : Prop := ∀ i, 1 ≤ e i ∧ e i ≤ κ

/-- Row-sum bound on the frequency of a zero of the homogeneous contact form. -/
theorem abs_freq_le_of_homContact (A : Matrix (Fin n) (Fin n) ℝ) {κ : ℝ}
    {x : (Fin n → ℝ) × ℝ} (hbox : ∀ i, 0 ≤ x.1 i ∧ x.1 i ≤ κ) (hx : homContact A x = 0) :
    |x.2| ≤ κ * ∑ i, ∑ j, |A i j| := by
  obtain ⟨v, hv0, hv⟩ := (homContact_eq_zero_iff A x).mp hx
  have hne : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  obtain ⟨k, hk⟩ := hne
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖) ⟨k, Finset.mem_univ k⟩
  have hvi₀ : 0 < ‖v i₀‖ := lt_of_lt_of_le (norm_pos_iff.mpr hk) (hi₀ k (Finset.mem_univ k))
  have hκ0 : 0 ≤ κ := le_trans (hbox i₀).1 (hbox i₀).2
  have heq := hv i₀
  simp only [Matrix.mulVec, dotProduct, complexify, rightScale] at heq
  have hlhs : ‖((x.2 : ℂ) * Complex.I) * v i₀‖ = |x.2| * ‖v i₀‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hbound : ‖∑ j, ((A i₀ j * x.1 j : ℝ) : ℂ) * v j‖ ≤
      (κ * ∑ j, |A i₀ j|) * ‖v i₀‖ := by
    calc ‖∑ j, ((A i₀ j * x.1 j : ℝ) : ℂ) * v j‖
        ≤ ∑ j, ‖((A i₀ j * x.1 j : ℝ) : ℂ) * v j‖ := norm_sum_le _ _
      _ ≤ ∑ j, (κ * |A i₀ j|) * ‖v i₀‖ := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (hbox j).1]
          have h1 : |A i₀ j| * x.1 j ≤ κ * |A i₀ j| := by
            rw [mul_comm κ]
            exact mul_le_mul_of_nonneg_left (hbox j).2 (abs_nonneg _)
          have h2 : ‖v j‖ ≤ ‖v i₀‖ := hi₀ j (Finset.mem_univ j)
          calc |A i₀ j| * x.1 j * ‖v j‖ ≤ (κ * |A i₀ j|) * ‖v j‖ :=
                mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ ≤ (κ * |A i₀ j|) * ‖v i₀‖ :=
                mul_le_mul_of_nonneg_left h2 (mul_nonneg hκ0 (abs_nonneg _))
      _ = (κ * ∑ j, |A i₀ j|) * ‖v i₀‖ := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [heq, hlhs] at hbound
  have hrow : ∑ j, |A i₀ j| ≤ ∑ i, ∑ j, |A i j| :=
    Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
      (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i₀)
  have h3 : |x.2| ≤ κ * ∑ j, |A i₀ j| := le_of_mul_le_mul_right hbound hvi₀
  calc |x.2| ≤ κ * ∑ j, |A i₀ j| := h3
    _ ≤ κ * ∑ i, ∑ j, |A i j| := mul_le_mul_of_nonneg_left hrow hκ0

/-- A contact in `K_κ` gives a zero of the homogeneous form on `[1, κ]ⁿ × (0, ∞)`. -/
theorem exists_box_of_cone_contact {κ : ℝ} (A : Matrix (Fin n) (Fin n) ℝ) {d : Fin n → ℝ}
    (hd : InCone κ d) (hc : contactDet A d = 0) :
    ∃ x : (Fin n → ℝ) × ℝ, InBox κ x.1 ∧ 0 < x.2 ∧ homContact A x = 0 := by
  have hn : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : contactDet A d = 1 := by
      unfold contactDet
      exact Matrix.det_isEmpty
    rw [h1] at hc
    exact one_ne_zero hc
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  have hm : 0 < d j₀ := hd.1 j₀
  refine ⟨(fun i => (d j₀)⁻¹ * d i, (d j₀)⁻¹), fun i => ⟨?_, ?_⟩, inv_pos.mpr hm, ?_⟩
  · show 1 ≤ (d j₀)⁻¹ * d i
    rw [inv_mul_eq_div, le_div_iff₀ hm, one_mul]
    exact hj₀ i (Finset.mem_univ i)
  · show (d j₀)⁻¹ * d i ≤ κ
    rw [inv_mul_eq_div, div_le_iff₀ hm]
    exact hd.2 i j₀
  · rw [homContact_eq_zero_iff_contact A _ (inv_pos.mpr hm)]
    have he : (fun i => ((d j₀)⁻¹)⁻¹ * ((d j₀)⁻¹ * d i)) = d := by
      funext i
      rw [inv_inv, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
    rw [he]
    exact hc

theorem cone_contact_of_box {κ : ℝ} (hκ : 1 ≤ κ) (A : Matrix (Fin n) (Fin n) ℝ)
    {x : (Fin n → ℝ) × ℝ} (hbox : InBox κ x.1) (hω : 0 < x.2) (hx : homContact A x = 0) :
    ∃ d, InCone κ d ∧ contactDet A d = 0 := by
  refine ⟨fun i => x.2⁻¹ * x.1 i, ⟨fun i => ?_, fun i j => ?_⟩, ?_⟩
  · exact mul_pos (inv_pos.mpr hω) (lt_of_lt_of_le one_pos (hbox i).1)
  · have h1 : x.1 i ≤ κ * x.1 j :=
      calc x.1 i ≤ κ := (hbox i).2
        _ = κ * 1 := (mul_one κ).symm
        _ ≤ κ * x.1 j := mul_le_mul_of_nonneg_left (hbox j).1 (by linarith)
    calc x.2⁻¹ * x.1 i ≤ x.2⁻¹ * (κ * x.1 j) :=
          mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hω).le
      _ = κ * (x.2⁻¹ * x.1 j) := by ring
  · have hx' : homContact A (x.1, x.2) = 0 := hx
    exact (homContact_eq_zero_iff_contact A x.1 hω).mp hx'

/-! ## Fritz-John points on the faces of the box (Theorem A4) -/

/-- Fritz-John point of `φ` on the zero set of the homogeneous contact form, relative to the face
of `[1, κ]ⁿ × (0, ∞)` containing it: the multiplier functional vanishes on every direction that
keeps the coordinates sitting at a bound (`e i = 1` or `e i = κ`) fixed. -/
def BoxFaceCritical (κ : ℝ) (φ : (Fin n → ℝ) × ℝ → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : (Fin n → ℝ) × ℝ) : Prop :=
  InBox κ x.1 ∧ 0 < x.2 ∧ homContact A x = 0 ∧
    ∃ Λ : Fin 2 → ℝ, ∃ Λ₀ : ℝ, (Λ, Λ₀) ≠ 0 ∧
      ∀ v : (Fin n → ℝ) × ℝ, (∀ i, (x.1 i = 1 ∨ x.1 i = κ) → v.1 i = 0) →
        Λ 0 * fderiv ℝ (fun y => (homContact A y).re) x v +
          Λ 1 * fderiv ℝ (fun y => (homContact A y).im) x v + Λ₀ * fderiv ℝ φ x v = 0

theorem exists_boxFaceCritical {κ : ℝ} {φ : (Fin n → ℝ) × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) {A : Matrix (Fin n) (Fin n) ℝ} (hA : HurwitzStable A)
    {d : Fin n → ℝ} (hd : InCone κ d) (hc : contactDet A d = 0) :
    ∃ x, BoxFaceCritical κ φ A x := by
  classical
  obtain ⟨x₀, hx₀box, hx₀pos, hx₀⟩ := exists_box_of_cone_contact A hd hc
  set W : ℝ := κ * ∑ i, ∑ j, |A i j| + 1 with hW
  have hbound : ∀ x : (Fin n → ℝ) × ℝ, InBox κ x.1 → homContact A x = 0 → |x.2| < W := by
    intro x hx hG
    have h := abs_freq_le_of_homContact A
      (fun i => ⟨le_trans zero_le_one (hx i).1, (hx i).2⟩) hG
    linarith
  let box : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 1 κ)
  have hbox_iff : ∀ e, e ∈ box ↔ InBox κ e := by
    intro e
    simp only [box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, InBox]
  let Z : Set ((Fin n → ℝ) × ℝ) := (box ×ˢ Set.Icc 0 W) ∩ {x | homContact A x = 0}
  have hZc : IsCompact Z :=
    ((isCompact_univ_pi (fun _ => isCompact_Icc)).prod isCompact_Icc).inter_right
      (isClosed_eq (homContact_contDiff A).continuous continuous_const)
  have hx₀Z : x₀ ∈ Z := by
    refine ⟨⟨(hbox_iff _).mpr hx₀box, hx₀pos.le, ?_⟩, hx₀⟩
    have := hbound x₀ hx₀box hx₀
    rw [abs_of_pos hx₀pos] at this
    exact this.le
  obtain ⟨xs, hxsZ, hmin⟩ := hZc.exists_isMinOn ⟨x₀, hx₀Z⟩ hφ.continuous.continuousOn
  have hxsbox : InBox κ xs.1 := (hbox_iff _).mp hxsZ.1.1
  have hxsG : homContact A xs = 0 := hxsZ.2
  have hxs_nonneg : 0 ≤ xs.2 := hxsZ.1.2.1
  have hxs_lt : xs.2 < W := lt_of_le_of_lt (le_abs_self _) (hbound xs hxsbox hxsG)
  have hxs_pos : 0 < xs.2 := by
    rcases eq_or_lt_of_le hxs_nonneg with h0 | h0
    · exfalso
      obtain ⟨v, hv⟩ := (homContact_eq_zero_iff A xs).mp hxsG
      rw [← h0] at hv
      simp only [Complex.ofReal_zero, zero_mul] at hv
      exact no_zero_eigen_of_hurwitz A hA xs.1
        (fun i => lt_of_lt_of_le one_pos (hxsbox i).1) v hv
    · exact h0
  -- the active (bound) coordinates
  let B := {i : Fin n // xs.1 i = 1 ∨ xs.1 i = κ}
  let L : B → StrongDual ℝ ((Fin n → ℝ) × ℝ) := fun b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b.1).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)
  have hL : ∀ b : B, ∀ y : (Fin n → ℝ) × ℝ, L b y = y.1 b.1 := fun b y => rfl
  let gRe : (Fin n → ℝ) × ℝ → ℝ := fun y => (homContact A y).re
  let gIm : (Fin n → ℝ) × ℝ → ℝ := fun y => (homContact A y).im
  have hgRe : ContDiff ℝ 1 gRe := Complex.reCLM.contDiff.comp (homContact_contDiff A)
  have hgIm : ContDiff ℝ 1 gIm := Complex.imCLM.contDiff.comp (homContact_contDiff A)
  let f : Fin 2 ⊕ B → (Fin n → ℝ) × ℝ → ℝ := fun k =>
    match k with
    | Sum.inl 0 => gRe
    | Sum.inl 1 => gIm
    | Sum.inr b => fun y => L b y
  let f' : Fin 2 ⊕ B → StrongDual ℝ ((Fin n → ℝ) × ℝ) := fun k =>
    match k with
    | Sum.inl 0 => fderiv ℝ gRe xs
    | Sum.inl 1 => fderiv ℝ gIm xs
    | Sum.inr b => L b
  have hf' : ∀ k, HasStrictFDerivAt (f k) (f' k) xs := by
    intro k
    rcases k with k | b
    · fin_cases k
      · exact (hgRe.contDiffAt).hasStrictFDerivAt one_ne_zero
      · exact (hgIm.contDiffAt).hasStrictFDerivAt one_ne_zero
    · exact (L b).hasStrictFDerivAt
  have hφ' : HasStrictFDerivAt φ (fderiv ℝ φ xs) xs :=
    (hφ.contDiffAt).hasStrictFDerivAt one_ne_zero
  -- local minimality on the constraint set
  have hfree : ∀ᶠ y in 𝓝 xs, ∀ i : Fin n, ¬ (xs.1 i = 1 ∨ xs.1 i = κ) →
      1 < y.1 i ∧ y.1 i < κ := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : xs.1 i = 1 ∨ xs.1 i = κ
    · exact Filter.Eventually.of_forall fun y h => absurd hi h
    · push Not at hi
      have hmem : xs.1 i ∈ Set.Ioo 1 κ :=
        ⟨lt_of_le_of_ne (hxsbox i).1 (Ne.symm hi.1), lt_of_le_of_ne (hxsbox i).2 hi.2⟩
      have hc : Continuous (fun y : (Fin n → ℝ) × ℝ => y.1 i) :=
        (continuous_apply i).comp continuous_fst
      filter_upwards [hc.continuousAt.eventually (isOpen_Ioo.mem_nhds hmem)] with y hy _
      exact hy
  have hω : ∀ᶠ y in 𝓝 xs, 0 < y.2 ∧ y.2 < W := by
    have hc : Continuous (fun y : (Fin n → ℝ) × ℝ => y.2) := continuous_snd
    have hmem : xs.2 ∈ Set.Ioo 0 W := ⟨hxs_pos, hxs_lt⟩
    filter_upwards [hc.continuousAt.eventually (isOpen_Ioo.mem_nhds hmem)] with y hy
    exact hy
  have hloc : IsLocalMinOn φ {y | ∀ k, f k y = f k xs} xs := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hfree, mem_nhdsWithin_of_mem_nhds hω,
      self_mem_nhdsWithin] with y hyfree hyω hyS
    have hyRe : gRe y = gRe xs := hyS (Sum.inl 0)
    have hyIm : gIm y = gIm xs := hyS (Sum.inl 1)
    have hyG : homContact A y = 0 := by
      apply Complex.ext
      · have : (homContact A y).re = (homContact A xs).re := hyRe
        rw [this, hxsG, Complex.zero_re]
      · have : (homContact A y).im = (homContact A xs).im := hyIm
        rw [this, hxsG, Complex.zero_im]
    have hybox : InBox κ y.1 := by
      intro i
      by_cases hi : xs.1 i = 1 ∨ xs.1 i = κ
      · have h : y.1 i = xs.1 i := hyS (Sum.inr ⟨i, hi⟩)
        rw [h]
        exact hxsbox i
      · exact ⟨(hyfree i hi).1.le, (hyfree i hi).2.le⟩
    exact hmin ⟨⟨(hbox_iff _).mpr hybox, hyω.1.le, hyω.2.le⟩, hyG⟩
  obtain ⟨Λ', Λ₀, hne, hsum⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt (Or.inl hloc) hf' hφ'
  have hsum' : ∀ v : (Fin n → ℝ) × ℝ,
      Λ' (Sum.inl 0) * fderiv ℝ gRe xs v + Λ' (Sum.inl 1) * fderiv ℝ gIm xs v +
        (∑ b : B, Λ' (Sum.inr b) * v.1 b.1) + Λ₀ * fderiv ℝ φ xs v = 0 := by
    intro v
    have h := congrArg (fun F : StrongDual ℝ ((Fin n → ℝ) × ℝ) => F v) hsum
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
      ContinuousLinearMap.zero_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    simpa [f', hL, add_assoc] using h
  refine ⟨xs, hxsbox, hxs_pos, hxsG, fun k => Λ' (Sum.inl k), Λ₀, ?_, ?_⟩
  · intro h0
    apply hne
    simp only [Prod.mk_eq_zero] at h0 ⊢
    refine ⟨?_, h0.2⟩
    have hl : ∀ k : Fin 2, Λ' (Sum.inl k) = 0 := fun k => congrFun h0.1 k
    have hr : ∀ b : B, Λ' (Sum.inr b) = 0 := by
      intro b
      have h := hsum' (Pi.single b.1 1, 0)
      rw [hl 0, hl 1, h0.2] at h
      simp only [zero_mul, zero_add, add_zero] at h
      rw [Finset.sum_eq_single b] at h
      · simpa using h
      · intro b' _ hb'
        have : b'.1 ≠ b.1 := fun e => hb' (Subtype.ext e)
        simp [this]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    funext k
    rcases k with k | b
    · exact hl k
    · exact hr b
  · intro v hv
    have h := hsum' v
    have hB : ∑ b : B, Λ' (Sum.inr b) * v.1 b.1 = 0 :=
      Finset.sum_eq_zero fun b _ => by rw [hv b.1 b.2, mul_zero]
    rw [hB, add_zero] at h
    exact h

/-- **Theorem A4 (bounded time-scale stability).**  For `κ ≥ 1` and any C¹ function `φ`,
`A · diag d` is Hurwitz for every `d ∈ K_κ` iff `A` is Hurwitz and the homogeneous contact form
has no Fritz-John point of `φ` on any face of `[1, κ]ⁿ × (0, ∞)`. -/
theorem kStable_iff_no_boxFaceCritical {κ : ℝ} (hκ : 1 ≤ κ) {φ : (Fin n → ℝ) × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (A : Matrix (Fin n) (Fin n) ℝ) :
    KStable κ A ↔ HurwitzStable A ∧ ¬ ∃ x, BoxFaceCritical κ φ A x := by
  rw [kStable_iff_no_cone_contact hκ]
  constructor
  · rintro ⟨hH, hno⟩
    refine ⟨hH, ?_⟩
    rintro ⟨x, hbox, hω, hG, -⟩
    exact hno (cone_contact_of_box hκ A hbox hω hG)
  · rintro ⟨hH, hno⟩
    refine ⟨hH, ?_⟩
    rintro ⟨d, hd, hc⟩
    exact hno (exists_boxFaceCritical hφ hH hd hc)

end DStability5x5
