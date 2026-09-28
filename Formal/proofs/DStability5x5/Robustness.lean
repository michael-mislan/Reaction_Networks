import proofs.DStability5x5.ExplicitCriterion

/-!
# Regular contacts are robust (Theorem A2)

A positive contact `d*` of `A₀` (`contactDet A₀ d* = 0`) is *regular* when the real derivative of
`d ↦ contactDet A₀ d` at `d*`, an `ℝ`-linear map `ℝⁿ → ℂ ≅ ℝ²`, is surjective; explicitly
(`regular_iff_rank`) some `2 × 2` minor `Re ∂_i · Im ∂_j - Re ∂_j · Im ∂_i` of the partial
derivatives `partialPoly` is nonzero.

Main results.

* `exists_contact_near_of_regular`: every `A` near `A₀` has a positive contact near `d*`.
  Proof: `F (A, d) = (A, contactDet A d)` is `C¹` on the complete space
  `(Fin n → Fin n → ℝ) × (Fin n → ℝ)` with surjective strict derivative
  `(δA, δd) ↦ (δA, ∂_A g δA + ∂_d g δd)`, so `F` is open at `(A₀, d*)`
  (`HasStrictFDerivAt.map_nhds_eq_of_surj`).
* `not_dStable_near_of_regular`, `not_regular_of_mem_closure`: matrices in the closure of the
  D-stable set have only singular contacts (Corollary (a)).
* `isOpen_hasRegularContact`, `isOpen_hurwitz_regularContact`, `not_dStable_of_regularContact`:
  Hurwitz matrices with a regular contact form an open set of non-D-stable matrices
  (Corollary (b)).
-/

noncomputable section

open Matrix Filter Topology Set

namespace DStability5x5

open DUnstableCores DStabilityCharacterization.SpectralContinuation

variable {n : ℕ}

/-- A regular positive contact: the derivative of the contact map in the rates is onto `ℂ`. -/
def RegularContact (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : Prop :=
  (∀ i, 0 < d i) ∧ contactDet A d = 0 ∧ Function.Surjective (fderiv ℝ (contactDet A) d)

/-! ## The explicit rank-2 test -/

theorem fderiv_contactDet (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    fderiv ℝ (contactDet A) d = contactDeriv A d := by
  have hc := contactPoly_hasFDerivAt A d
  rw [← contactDet_eq_poly] at hc
  exact hc.fderiv

theorem fderiv_contactDet_single (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (contactDet A) d (Pi.single i 1) = partialPoly A d i := by
  rw [fderiv_contactDet, contactDeriv_single]

theorem clm_apply_eq_sum_single (L : (Fin n → ℝ) →L[ℝ] ℂ) (v : Fin n → ℝ) :
    L v = ∑ i, v i • L (Pi.single i 1) := by
  classical
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  calc L v = L (∑ i, v i • Pi.single i (1 : ℝ)) := congrArg L hv
    _ = ∑ i, v i • L (Pi.single i 1) := by simp only [map_sum, map_smul]

theorem cross_sum_eq (r m a b : Fin n → ℝ) :
    (∑ i, a i * r i) * (∑ j, b j * m j) - (∑ j, b j * r j) * (∑ i, a i * m i) =
      ∑ i, ∑ j, a i * b j * (r i * m j - r j * m i) := by
  have h2 : (∑ j, b j * r j) * (∑ i, a i * m i) = ∑ i, ∑ j, (a i * m i) * (b j * r j) := by
    rw [mul_comm (∑ j, b j * r j), Finset.sum_mul_sum]
  rw [Finset.sum_mul_sum, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Explicit regularity test.**  The derivative of the contact map is onto `ℂ` iff some
`2 × 2` minor of the matrix `[Re ∂_i ; Im ∂_i]` of explicit partial derivatives is nonzero. -/
theorem regular_iff_rank (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    Function.Surjective (fderiv ℝ (contactDet A) d) ↔
      ∃ i j : Fin n, (partialPoly A d i).re * (partialPoly A d j).im -
        (partialPoly A d j).re * (partialPoly A d i).im ≠ 0 := by
  have hsum : ∀ v, fderiv ℝ (contactDet A) d v = ∑ i, v i • partialPoly A d i := by
    intro v
    rw [clm_apply_eq_sum_single]
    simp only [fderiv_contactDet_single]
  have hre : ∀ v, (fderiv ℝ (contactDet A) d v).re = ∑ i, v i * (partialPoly A d i).re := by
    intro v
    rw [hsum v, Complex.re_sum]
    simp only [Complex.smul_re, smul_eq_mul]
  have him : ∀ v, (fderiv ℝ (contactDet A) d v).im = ∑ i, v i * (partialPoly A d i).im := by
    intro v
    rw [hsum v, Complex.im_sum]
    simp only [Complex.smul_im, smul_eq_mul]
  constructor
  · intro hs
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha⟩ := hs 1
    obtain ⟨b, hb⟩ := hs Complex.I
    have ha1 := hre a
    have ha2 := him a
    have hb1 := hre b
    have hb2 := him b
    rw [ha] at ha1 ha2
    rw [hb] at hb1 hb2
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] at ha1 ha2 hb1 hb2
    have hx := cross_sum_eq (fun i => (partialPoly A d i).re) (fun i => (partialPoly A d i).im) a b
    rw [← ha1, ← ha2, ← hb1, ← hb2] at hx
    have hzero : ∑ i, ∑ j, a i * b j *
        ((partialPoly A d i).re * (partialPoly A d j).im -
          (partialPoly A d j).re * (partialPoly A d i).im) = 0 := by
      simp [hcon]
    rw [hzero] at hx
    norm_num at hx
  · rintro ⟨i, j, hD⟩ w
    refine ⟨((w.re * (partialPoly A d j).im - (partialPoly A d j).re * w.im) /
        ((partialPoly A d i).re * (partialPoly A d j).im -
          (partialPoly A d j).re * (partialPoly A d i).im)) • Pi.single i 1 +
      (((partialPoly A d i).re * w.im - w.re * (partialPoly A d i).im) /
        ((partialPoly A d i).re * (partialPoly A d j).im -
          (partialPoly A d j).re * (partialPoly A d i).im)) • Pi.single j 1, ?_⟩
    rw [map_add, map_smul, map_smul, fderiv_contactDet_single, fderiv_contactDet_single]
    generalize partialPoly A d i = p at hD ⊢
    generalize partialPoly A d j = q at hD ⊢
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
      ring
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
      ring

/-! ## The joint contact map -/

/-- Matrix entries as a plain function space (Pi sup norm, complete). -/
abbrev Ent (n : ℕ) := Fin n → Fin n → ℝ

/-- The contact determinant as a function of the matrix entries and the rates jointly. -/
def contactJoint (p : Ent n × (Fin n → ℝ)) : ℂ := contactDet p.1 p.2

/-- The map `F (A, d) = (A, contactDet A d)`. -/
def contactMap (p : Ent n × (Fin n → ℝ)) : Ent n × ℂ := (p.1, contactJoint p)

theorem contactJoint_contDiff : ContDiff ℝ 1 (contactJoint (n := n)) := by
  unfold contactJoint contactDet
  simp_rw [Matrix.det_apply]
  apply ContDiff.sum
  intro σ _
  simp only [Units.smul_def, zsmul_eq_mul]
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  simp only [Matrix.sub_apply, Matrix.smul_apply, complexify, rightScale]
  apply ContDiff.sub contDiff_const
  have h : ContDiff ℝ 1 (fun p : Ent n × (Fin n → ℝ) => p.1 (σ i) i * p.2 i) :=
    ((contDiff_apply_apply ℝ ℝ (σ i) i).comp contDiff_fst).mul
      ((contDiff_apply ℝ ℝ i).comp contDiff_snd)
  exact Complex.ofRealCLM.contDiff.comp h

theorem hasFDerivAt_contactJoint (p : Ent n × (Fin n → ℝ)) :
    HasFDerivAt contactJoint (fderiv ℝ contactJoint p) p :=
  (contactJoint_contDiff.differentiable one_ne_zero p).hasFDerivAt

/-- The rate derivative is the joint derivative restricted to rate directions. -/
theorem fderiv_contactDet_eq_comp (A : Ent n) (d : Fin n → ℝ) :
    fderiv ℝ (contactDet A) d =
      (fderiv ℝ contactJoint (A, d)).comp (ContinuousLinearMap.inr ℝ (Ent n) (Fin n → ℝ)) := by
  have h := (hasFDerivAt_contactJoint (A, d)).comp d (hasFDerivAt_prodMk_right A d)
  exact h.fderiv

theorem partialPoly_eq_fderiv (A : Ent n) (d : Fin n → ℝ) (i : Fin n) :
    partialPoly A d i = fderiv ℝ contactJoint (A, d) (0, Pi.single i 1) := by
  rw [← fderiv_contactDet_single, fderiv_contactDet_eq_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]

theorem continuous_partialPoly (i : Fin n) :
    Continuous (fun p : Ent n × (Fin n → ℝ) => partialPoly p.1 p.2 i) := by
  have h := (contactJoint_contDiff.continuous_fderiv one_ne_zero).clm_apply
    (continuous_const : Continuous fun _ : Ent n × (Fin n → ℝ) =>
      ((0 : Ent n), (Pi.single i (1 : ℝ) : Fin n → ℝ)))
  refine h.congr fun p => ?_
  exact (partialPoly_eq_fderiv p.1 p.2 i).symm

/-! ## Openness of the contact map at a regular contact -/

/-- At a contact where the rate derivative is onto, every nearby matrix has a contact whose
matrix–rate pair lies in any prescribed neighbourhood of `(A₀, d₀)`. -/
theorem eventually_exists_contact_mem (A₀ : Ent n) (d₀ : Fin n → ℝ)
    (h0 : contactDet A₀ d₀ = 0) (hs : Function.Surjective (fderiv ℝ (contactDet A₀) d₀))
    {W : Set (Ent n × (Fin n → ℝ))} (hW : W ∈ 𝓝 (A₀, d₀)) :
    ∀ᶠ A in 𝓝 A₀, ∃ d, (A, d) ∈ W ∧ contactDet A d = 0 := by
  have hG : HasStrictFDerivAt contactJoint (fderiv ℝ contactJoint (A₀, d₀)) (A₀, d₀) :=
    contactJoint_contDiff.contDiffAt.hasStrictFDerivAt one_ne_zero
  have hcomp := fderiv_contactDet_eq_comp A₀ d₀
  generalize hL : fderiv ℝ (contactJoint (n := n)) (A₀, d₀) = L at hG hcomp
  have hΦ : HasStrictFDerivAt contactMap
      ((ContinuousLinearMap.fst ℝ (Ent n) (Fin n → ℝ)).prod L) (A₀, d₀) :=
    hasStrictFDerivAt_fst.prodMk hG
  have hsurj : Function.Surjective ((ContinuousLinearMap.fst ℝ (Ent n) (Fin n → ℝ)).prod L) := by
    rintro ⟨δA, w⟩
    obtain ⟨δd, hδd⟩ := hs (w - L (δA, 0))
    rw [hcomp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hδd
    refine ⟨(δA, δd), ?_⟩
    rw [ContinuousLinearMap.prod_apply]
    refine Prod.ext rfl ?_
    show L (δA, δd) = w
    have hsplit : ((δA, δd) : Ent n × (Fin n → ℝ)) = (δA, 0) + (0, δd) := by simp
    rw [hsplit, map_add, hδd]
    ring
  have hmap := hΦ.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)
  have hΦ0 : contactMap (A₀, d₀) = (A₀, (0 : ℂ)) := by
    show ((A₀, contactDet A₀ d₀) : Ent n × ℂ) = (A₀, 0)
    rw [h0]
  have himg : contactMap '' W ∈ 𝓝 (A₀, (0 : ℂ)) := by
    have h1 := image_mem_map (m := contactMap) hW
    rw [hmap, hΦ0] at h1
    exact h1
  have hpre : (fun A : Ent n => (A, (0 : ℂ))) ⁻¹' (contactMap '' W) ∈ 𝓝 A₀ :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds himg
  filter_upwards [hpre] with A hA
  obtain ⟨⟨B, d⟩, hBW, hBd⟩ := hA
  simp only [contactMap, contactJoint, Prod.mk.injEq] at hBd
  obtain ⟨rfl, hc⟩ := hBd
  exact ⟨d, hBW, hc⟩

/-! ## Theorem A2 and its corollaries -/

theorem isOpen_pos_rates :
    IsOpen {p : Ent n × (Fin n → ℝ) | ∀ i, 0 < p.2 i} := by
  rw [setOf_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const ((continuous_apply i).comp continuous_snd)

/-- **Theorem A2 (regular contacts are robust).**  Every matrix near `A₀` has a positive contact
within `ε` of a regular contact of `A₀`. -/
theorem exists_contact_near_of_regular (A₀ : Matrix (Fin n) (Fin n) ℝ) (d₀ : Fin n → ℝ)
    (h : RegularContact A₀ d₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ A in 𝓝 A₀, ∃ d, (∀ i, 0 < d i) ∧ dist d d₀ < ε ∧ contactDet A d = 0 := by
  have h2 : IsOpen {p : Ent n × (Fin n → ℝ) | dist p.2 d₀ < ε} :=
    isOpen_lt (continuous_snd.dist continuous_const) continuous_const
  have hW : {p : Ent n × (Fin n → ℝ) | ∀ i, 0 < p.2 i} ∩ {p | dist p.2 d₀ < ε} ∈
      𝓝 ((A₀ : Ent n), d₀) :=
    (isOpen_pos_rates.inter h2).mem_nhds ⟨h.1, by simpa using hε⟩
  have hev := eventually_exists_contact_mem (A₀ : Ent n) d₀ h.2.1 h.2.2 hW
  exact hev.mono fun A hA => by
    obtain ⟨d, ⟨hd, hdist⟩, hc⟩ := hA
    exact ⟨d, hd, hdist, hc⟩

/-- A positive contact excludes D-stability. -/
theorem not_dStable_of_contact (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) (hc : contactDet A d = 0) : ¬ DStable A := by
  intro hA
  obtain ⟨v, hv⟩ := (contact_iff_eigenpair A d).mp hc
  have h := hA d hd Complex.I v hv
  simp at h

theorem not_dStable_of_regularContact (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (h : RegularContact A d) : ¬ DStable A :=
  not_dStable_of_contact A d h.1 h.2.1

theorem not_dStable_near_of_regular (A₀ : Matrix (Fin n) (Fin n) ℝ) (d₀ : Fin n → ℝ)
    (h : RegularContact A₀ d₀) : ∀ᶠ A in 𝓝 A₀, ¬ DStable A :=
  (exists_contact_near_of_regular A₀ d₀ h one_pos).mono fun A hA => by
    obtain ⟨d, hd, -, hc⟩ := hA
    exact not_dStable_of_contact A d hd hc

/-- **Corollary (a).**  A matrix in the closure of the D-stable set has no regular contact. -/
theorem not_regular_of_mem_closure (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (hA : A₀ ∈ closure {A : Matrix (Fin n) (Fin n) ℝ | DStable A}) (d : Fin n → ℝ) :
    ¬ RegularContact A₀ d := by
  intro h
  obtain ⟨B, hB1, hB2⟩ :=
    mem_closure_iff_nhds.mp hA {A | ¬ DStable A} (not_dStable_near_of_regular A₀ d h)
  simp only [Set.mem_setOf_eq] at hB1 hB2
  exact hB1 hB2

/-- Having a regular contact is an open condition on the matrix. -/
theorem isOpen_hasRegularContact :
    IsOpen {A : Matrix (Fin n) (Fin n) ℝ | ∃ d, RegularContact A d} := by
  rw [isOpen_iff_mem_nhds]
  rintro A₀ ⟨d₀, h⟩
  obtain ⟨i, j, hij⟩ := (regular_iff_rank A₀ d₀).mp h.2.2
  have hcont : Continuous (fun p : Ent n × (Fin n → ℝ) =>
      (partialPoly p.1 p.2 i).re * (partialPoly p.1 p.2 j).im -
        (partialPoly p.1 p.2 j).re * (partialPoly p.1 p.2 i).im) := by
    have hi := continuous_partialPoly (n := n) i
    have hj := continuous_partialPoly (n := n) j
    exact ((Complex.continuous_re.comp hi).mul (Complex.continuous_im.comp hj)).sub
      ((Complex.continuous_re.comp hj).mul (Complex.continuous_im.comp hi))
  have h3 : IsOpen {p : Ent n × (Fin n → ℝ) |
      (partialPoly p.1 p.2 i).re * (partialPoly p.1 p.2 j).im -
        (partialPoly p.1 p.2 j).re * (partialPoly p.1 p.2 i).im ≠ 0} :=
    isOpen_ne_fun hcont continuous_const
  have hW := (isOpen_pos_rates.inter h3).mem_nhds (x := ((A₀ : Ent n), d₀)) ⟨h.1, hij⟩
  have hev := eventually_exists_contact_mem (A₀ : Ent n) d₀ h.2.1 h.2.2 hW
  exact hev.mono fun A hA => by
    obtain ⟨d, ⟨hd, hr⟩, hc⟩ := hA
    exact ⟨d, hd, hc, (regular_iff_rank A d).mpr ⟨i, j, hr⟩⟩

/-- **Corollary (b).**  Hurwitz matrices with a regular contact form an open set. -/
theorem isOpen_hurwitz_regularContact :
    IsOpen {A : Matrix (Fin n) (Fin n) ℝ | HurwitzStable A ∧ ∃ d, RegularContact A d} :=
  isOpen_hurwitzStable.inter isOpen_hasRegularContact

/-- **Corollary (b), packaged.**  The Hurwitz matrices with a regular contact form an open set
of non-D-stable matrices. -/
theorem hurwitz_regularContact_open_not_dStable :
    IsOpen {A : Matrix (Fin n) (Fin n) ℝ | HurwitzStable A ∧ ∃ d, RegularContact A d} ∧
      ∀ A ∈ {A : Matrix (Fin n) (Fin n) ℝ | HurwitzStable A ∧ ∃ d, RegularContact A d},
        ¬ DStable A := by
  refine ⟨isOpen_hurwitz_regularContact, ?_⟩
  rintro A ⟨-, d, hd⟩
  exact not_dStable_of_regularContact A d hd

end DStability5x5
