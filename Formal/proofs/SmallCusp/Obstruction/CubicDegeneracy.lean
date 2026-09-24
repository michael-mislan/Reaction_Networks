import proofs.SmallCusp.Obstruction.ConicFold

/-!
# Four-chart cubic-degeneracy obstruction

A nonzero singular planar Jacobian has a nonzero row and a nonzero column.
Their perpendiculars generate its right and left kernels.  The four possible
row/column choices are therefore a complete generator chart, not an
enumeration of kernel vectors.
-/

namespace SmallCusp

def alternateRightKernel {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) : Species → ℝ := ![
  Q.jacobian v unitState 1 1,
  -Q.jacobian v unitState 1 0
]

def alternateLeftKernel {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) : Species → ℝ := ![
  Q.jacobian v unitState 1 1,
  -Q.jacobian v unitState 0 1
]

def rightChartGuard {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) (alternate : Bool) : Prop :=
  if alternate then
    Q.jacobian v unitState 0 0 = 0 ∧ Q.jacobian v unitState 0 1 = 0
  else True

def leftChartGuard {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) (alternate : Bool) : Prop :=
  if alternate then
    Q.jacobian v unitState 0 0 = 0 ∧ Q.jacobian v unitState 1 0 = 0
  else True

def chartRightKernel {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) (alternate : Bool) : Species → ℝ :=
  if alternate then alternateRightKernel Q v else canonicalRightKernel Q v

def chartLeftKernel {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) (alternate : Bool) : Species → ℝ :=
  if alternate then alternateLeftKernel Q v else canonicalLeftKernel Q v

def ChartCubicDegenerate {m : ℕ} (Q : SmallPlanarNetwork m)
    (rightAlternate leftAlternate : Bool) : Prop :=
  ∀ (v : Fin m → ℝ) (h : Species → ℝ),
    PositiveVector v →
    (∀ s, Q.massAction v unitState s = 0) →
    unitJacobianDet Q v = 0 →
    rightChartGuard Q v rightAlternate →
    leftChartGuard Q v leftAlternate →
    dot (chartLeftKernel Q v leftAlternate)
        (Q.hessianApply v unitState
          (chartRightKernel Q v rightAlternate)
          (chartRightKernel Q v rightAlternate)) = 0 →
    (∀ i, Q.jacobianApply v unitState h i =
      -Q.hessianApply v unitState
        (chartRightKernel Q v rightAlternate)
        (chartRightKernel Q v rightAlternate) i) →
    dot (chartLeftKernel Q v leftAlternate)
      (Q.hessianApply v unitState
        (chartRightKernel Q v rightAlternate) h) = 0

def FourChartCubicDegenerate {m : ℕ} (Q : SmallPlanarNetwork m) : Prop :=
  ∀ r l : Bool, ChartCubicDegenerate Q r l

def PositiveEquilibriumJacobianNonzero {m : ℕ}
    (Q : SmallPlanarNetwork m) : Prop :=
  ∀ v : Fin m → ℝ, PositiveVector v →
    (∀ s, Q.massAction v unitState s = 0) →
    Q.jacobian v unitState 0 0 ≠ 0 ∨
    Q.jacobian v unitState 0 1 ≠ 0 ∨
    Q.jacobian v unitState 1 0 ≠ 0 ∨
    Q.jacobian v unitState 1 1 ≠ 0

private theorem finTwo_ne_zero_components (u : Species → ℝ) (hu : u ≠ 0) :
    u 0 ≠ 0 ∨ u 1 ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  apply hu
  funext i
  fin_cases i <;> simp [h.1, h.2]

private theorem perpendicular_proportional
    (a b x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0)
    (hkernel : a * x + b * y = 0) (hrow : b ≠ 0 ∨ a ≠ 0) :
    ∃ lam : ℝ, lam ≠ 0 ∧ b = lam * x ∧ -a = lam * y := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := hxy.resolve_left (fun hxne ↦ hxne hx)
    have hb : b = 0 := by
      rw [hx, mul_zero, zero_add] at hkernel
      exact (mul_eq_zero.mp hkernel).resolve_right hy
    have ha : a ≠ 0 := hrow.resolve_left (fun hbne ↦ hbne hb)
    let lam := -a / y
    refine ⟨lam, div_ne_zero (neg_ne_zero.mpr ha) hy, ?_, ?_⟩
    · simp [lam, hx, hb]
    · simp [lam, hy]
  · let lam := b / x
    have hb : b ≠ 0 := by
      intro hb
      rw [hb, zero_mul, add_zero] at hkernel
      have ha : a = 0 := (mul_eq_zero.mp hkernel).resolve_right hx
      exact hrow.resolve_left (fun hbne ↦ hbne hb) ha
    refine ⟨lam, div_ne_zero hb hx, ?_, ?_⟩
    · simp [lam, hx]
    · dsimp [lam]
      field_simp
      nlinarith

private theorem jacobianApply_scale {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) (u : Species → ℝ) (lam : ℝ) (i : Species) :
    Q.jacobianApply v unitState (fun j ↦ lam * u j) i =
      lam * Q.jacobianApply v unitState u i := by
  simp [SmallPlanarNetwork.jacobianApply, Fin.sum_univ_two]
  ring

private theorem hessianApply_scale {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) (u w : Species → ℝ) (lam mu : ℝ) (i : Species) :
    Q.hessianApply v unitState (fun j ↦ lam * u j) (fun j ↦ mu * w j) i =
      lam * mu * Q.hessianApply v unitState u w i := by
  simp [SmallPlanarNetwork.hessianApply, Fin.sum_univ_two]
  ring

private theorem dot_hessian_scale {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) (p q h : Species → ℝ) (mu lam rho : ℝ) :
    dot (fun i ↦ mu * p i)
      (Q.hessianApply v unitState (fun i ↦ lam * q i)
        (fun i ↦ rho * h i)) =
      mu * lam * rho * dot p (Q.hessianApply v unitState q h) := by
  simp [dot, SmallPlanarNetwork.hessianApply, Fin.sum_univ_two]
  ring

theorem fourChartCubicDegenerate_excludes_cusp_intrinsic {m : ℕ}
    (Q : SmallPlanarNetwork m)
    (hcharts : FourChartCubicDegenerate Q) :
    ¬ AdmitsTransverseCusp Q := by
  rintro ⟨C, hC⟩
  let D := normalizedTraceFreeCertificate C
  have hD : TraceFreeNormalizedValid D :=
    normalizedTraceFreeCertificate_valid C hC
  rcases hD with ⟨hstate, hv, heq, hright, hleft, hq, hp,
    hfold, hcenter, hcubic, _hunfold⟩
  have heqUnit : ∀ s, Q.massAction D.rates unitState s = 0 := by
    intro s
    simpa [hstate] using heq s
  have hrightUnit : ∀ i, Q.jacobianApply D.rates unitState D.rightKernel i = 0 := by
    intro i
    simpa [hstate] using hright i
  have hdetUnit : unitJacobianDet Q D.rates = 0 := by
    apply unitJacobianDet_eq_zero_of_rightKernel Q D.rates D.rightKernel hq
    exact hrightUnit
  have hleftUnit : ∀ j, ∑ i : Species,
      D.leftKernel i * Q.jacobian D.rates unitState i j = 0 := by
    intro j
    simpa [hstate] using hleft j
  have hcenterUnit : ∀ i, Q.jacobianApply D.rates unitState D.centerCorrection i =
      -Q.hessianApply D.rates unitState D.rightKernel D.rightKernel i := by
    intro i
    simpa [hstate] using hcenter i
  have hfoldUnit : dot D.leftKernel
      (Q.hessianApply D.rates unitState D.rightKernel D.rightKernel) = 0 := by
    simpa [hstate] using hfold
  have hcubicUnit : dot D.leftKernel
      (Q.hessianApply D.rates unitState D.rightKernel D.centerCorrection) ≠ 0 := by
    simpa [hstate] using hcubic
  have hqcomp := finTwo_ne_zero_components D.rightKernel hq
  have hpcomp := finTwo_ne_zero_components D.leftKernel hp
  have hJ' := normalizedTraceFreeCertificate_jacobian_nonzero C hC
  let a := Q.jacobian D.rates unitState 0 0
  let b := Q.jacobian D.rates unitState 0 1
  let c := Q.jacobian D.rates unitState 1 0
  let d := Q.jacobian D.rates unitState 1 1
  have hr0 := hrightUnit 0
  have hr1 := hrightUnit 1
  have hl0 := hleftUnit 0
  have hl1 := hleftUnit 1
  simp only [SmallPlanarNetwork.jacobianApply, Fin.sum_univ_two] at hr0 hr1
  simp only [Fin.sum_univ_two] at hl0 hl1
  change a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 at hJ'
  change a * D.rightKernel 0 + b * D.rightKernel 1 = 0 at hr0
  change c * D.rightKernel 0 + d * D.rightKernel 1 = 0 at hr1
  change D.leftKernel 0 * a + D.leftKernel 1 * c = 0 at hl0
  change D.leftKernel 0 * b + D.leftKernel 1 * d = 0 at hl1
  by_cases hrow0 : b ≠ 0 ∨ a ≠ 0
  · obtain ⟨lam, hlam, hq0, hq1⟩ :=
      perpendicular_proportional a b (D.rightKernel 0) (D.rightKernel 1)
        (finTwo_ne_zero_components _ hq) hr0 hrow0
    have hqchart : canonicalRightKernel Q D.rates =
        fun i ↦ lam * D.rightKernel i := by
      funext i
      fin_cases i <;> simp [canonicalRightKernel, a, b, hq0, hq1]
    by_cases hcol0 : c ≠ 0 ∨ a ≠ 0
    · obtain ⟨mu, hmu, hp0, hp1⟩ :=
        perpendicular_proportional a c (D.leftKernel 0) (D.leftKernel 1)
          (finTwo_ne_zero_components _ hp)
          (by nlinarith [hl0]) hcol0
      have hpchart : canonicalLeftKernel Q D.rates =
          fun i ↦ mu * D.leftKernel i := by
        funext i
        fin_cases i <;> simp [canonicalLeftKernel, a, c, hp0, hp1]
      let hh : Species → ℝ := fun i ↦ lam ^ 2 * D.centerCorrection i
      have hfoldChart : dot (canonicalLeftKernel Q D.rates)
          (Q.hessianApply D.rates unitState (canonicalRightKernel Q D.rates)
            (canonicalRightKernel Q D.rates)) = 0 := by
        rw [hqchart, hpchart, dot_hessian_scale]
        rw [hfoldUnit, mul_zero]
      have hcenterChart : ∀ i, Q.jacobianApply D.rates unitState hh i =
          -Q.hessianApply D.rates unitState (canonicalRightKernel Q D.rates)
            (canonicalRightKernel Q D.rates) i := by
        intro i
        rw [hqchart, jacobianApply_scale, hcenterUnit i,
          hessianApply_scale]
        ring
      have hzero := hcharts false false D.rates hh hv heqUnit hdetUnit trivial trivial
        hfoldChart hcenterChart
      have hscale := dot_hessian_scale Q D.rates D.leftKernel D.rightKernel
        D.centerCorrection mu lam (lam ^ 2)
      rw [← hpchart, ← hqchart] at hscale
      change dot (canonicalLeftKernel Q D.rates)
        (Q.hessianApply D.rates unitState (canonicalRightKernel Q D.rates) hh) = _
        at hscale
      have hzero' : dot (canonicalLeftKernel Q D.rates)
          (Q.hessianApply D.rates unitState (canonicalRightKernel Q D.rates) hh) = 0 := by
        simpa [chartLeftKernel, chartRightKernel] using hzero
      rw [hzero'] at hscale
      apply hcubicUnit
      apply (mul_eq_zero.mp hscale.symm).resolve_left
      exact mul_ne_zero (mul_ne_zero hmu hlam) (pow_ne_zero 2 hlam)
    · have hcZero : c = 0 := by
        by_contra hc
        exact hcol0 (Or.inl hc)
      have haZero : a = 0 := by
        by_contra ha
        exact hcol0 (Or.inr ha)
      have hcol1 : d ≠ 0 ∨ b ≠ 0 := by
        rcases hJ' with ha | hb | hc | hd
        · exact (ha haZero).elim
        · exact Or.inr hb
        · exact (hc hcZero).elim
        · exact Or.inl hd
      obtain ⟨mu, hmu, hp0, hp1⟩ :=
        perpendicular_proportional b d (D.leftKernel 0) (D.leftKernel 1)
          (finTwo_ne_zero_components _ hp) (by nlinarith [hl1]) hcol1
      have hpchart : alternateLeftKernel Q D.rates =
          fun i ↦ mu * D.leftKernel i := by
        funext i
        fin_cases i <;> simp [alternateLeftKernel, b, d, hp0, hp1]
      let hh : Species → ℝ := fun i ↦ lam ^ 2 * D.centerCorrection i
      have hguardL : leftChartGuard Q D.rates true := by
        change a = 0 ∧ c = 0
        exact ⟨haZero, hcZero⟩
      have hfoldChart : dot (alternateLeftKernel Q D.rates)
          (Q.hessianApply D.rates unitState (canonicalRightKernel Q D.rates)
            (canonicalRightKernel Q D.rates)) = 0 := by
        rw [hqchart, hpchart, dot_hessian_scale, hfoldUnit, mul_zero]
      have hcenterChart : ∀ i, Q.jacobianApply D.rates unitState hh i =
          -Q.hessianApply D.rates unitState (canonicalRightKernel Q D.rates)
            (canonicalRightKernel Q D.rates) i := by
        intro i
        rw [hqchart, jacobianApply_scale, hcenterUnit i, hessianApply_scale]
        ring
      have hzero := hcharts false true D.rates hh hv heqUnit hdetUnit trivial hguardL
        hfoldChart hcenterChart
      have hscale := dot_hessian_scale Q D.rates D.leftKernel D.rightKernel
        D.centerCorrection mu lam (lam ^ 2)
      rw [← hpchart, ← hqchart] at hscale
      change dot (alternateLeftKernel Q D.rates)
        (Q.hessianApply D.rates unitState (canonicalRightKernel Q D.rates) hh) = _
        at hscale
      have hzero' : dot (alternateLeftKernel Q D.rates)
          (Q.hessianApply D.rates unitState (canonicalRightKernel Q D.rates) hh) = 0 := by
        simpa [chartLeftKernel, chartRightKernel] using hzero
      rw [hzero'] at hscale
      apply hcubicUnit
      apply (mul_eq_zero.mp hscale.symm).resolve_left
      exact mul_ne_zero (mul_ne_zero hmu hlam) (pow_ne_zero 2 hlam)
  · have hbZero : b = 0 := by
      by_contra hb
      exact hrow0 (Or.inl hb)
    have haZero : a = 0 := by
      by_contra ha
      exact hrow0 (Or.inr ha)
    have hrow1 : d ≠ 0 ∨ c ≠ 0 := by
      rcases hJ' with ha | hb | hc | hd
      · exact (ha haZero).elim
      · exact (hb hbZero).elim
      · exact Or.inr hc
      · exact Or.inl hd
    obtain ⟨lam, hlam, hq0, hq1⟩ :=
      perpendicular_proportional c d (D.rightKernel 0) (D.rightKernel 1)
        (finTwo_ne_zero_components _ hq) hr1 hrow1
    have hqchart : alternateRightKernel Q D.rates =
        fun i ↦ lam * D.rightKernel i := by
      funext i
      fin_cases i <;> simp [alternateRightKernel, c, d, hq0, hq1]
    have hguardR : rightChartGuard Q D.rates true := by
      change a = 0 ∧ b = 0
      exact ⟨haZero, hbZero⟩
    by_cases hcol0 : c ≠ 0 ∨ a ≠ 0
    · obtain ⟨mu, hmu, hp0, hp1⟩ :=
        perpendicular_proportional a c (D.leftKernel 0) (D.leftKernel 1)
          (finTwo_ne_zero_components _ hp)
          (by nlinarith [hl0]) hcol0
      have hpchart : canonicalLeftKernel Q D.rates =
          fun i ↦ mu * D.leftKernel i := by
        funext i
        fin_cases i <;> simp [canonicalLeftKernel, a, c, hp0, hp1]
      let hh : Species → ℝ := fun i ↦ lam ^ 2 * D.centerCorrection i
      have hfoldChart : dot (canonicalLeftKernel Q D.rates)
          (Q.hessianApply D.rates unitState (alternateRightKernel Q D.rates)
            (alternateRightKernel Q D.rates)) = 0 := by
        rw [hqchart, hpchart, dot_hessian_scale, hfoldUnit, mul_zero]
      have hcenterChart : ∀ i, Q.jacobianApply D.rates unitState hh i =
          -Q.hessianApply D.rates unitState (alternateRightKernel Q D.rates)
            (alternateRightKernel Q D.rates) i := by
        intro i
        rw [hqchart, jacobianApply_scale, hcenterUnit i, hessianApply_scale]
        ring
      have hzero := hcharts true false D.rates hh hv heqUnit hdetUnit hguardR trivial
        hfoldChart hcenterChart
      have hscale := dot_hessian_scale Q D.rates D.leftKernel D.rightKernel
        D.centerCorrection mu lam (lam ^ 2)
      rw [← hpchart, ← hqchart] at hscale
      change dot (canonicalLeftKernel Q D.rates)
        (Q.hessianApply D.rates unitState (alternateRightKernel Q D.rates) hh) = _
        at hscale
      have hzero' : dot (canonicalLeftKernel Q D.rates)
          (Q.hessianApply D.rates unitState (alternateRightKernel Q D.rates) hh) = 0 := by
        simpa [chartLeftKernel, chartRightKernel] using hzero
      rw [hzero'] at hscale
      apply hcubicUnit
      apply (mul_eq_zero.mp hscale.symm).resolve_left
      exact mul_ne_zero (mul_ne_zero hmu hlam) (pow_ne_zero 2 hlam)
    · have hcZero : c = 0 := by
        by_contra hc
        exact hcol0 (Or.inl hc)
      have haZero' : a = 0 := by
        by_contra ha
        exact hcol0 (Or.inr ha)
      have hcol1 : d ≠ 0 ∨ b ≠ 0 := by
        rcases hJ' with ha | hb | hc | hd
        · exact (ha haZero').elim
        · exact Or.inr hb
        · exact (hc hcZero).elim
        · exact Or.inl hd
      obtain ⟨mu, hmu, hp0, hp1⟩ :=
        perpendicular_proportional b d (D.leftKernel 0) (D.leftKernel 1)
          (finTwo_ne_zero_components _ hp) (by nlinarith [hl1]) hcol1
      have hpchart : alternateLeftKernel Q D.rates =
          fun i ↦ mu * D.leftKernel i := by
        funext i
        fin_cases i <;> simp [alternateLeftKernel, b, d, hp0, hp1]
      let hh : Species → ℝ := fun i ↦ lam ^ 2 * D.centerCorrection i
      have hguardL : leftChartGuard Q D.rates true := by
        change a = 0 ∧ c = 0
        exact ⟨haZero', hcZero⟩
      have hfoldChart : dot (alternateLeftKernel Q D.rates)
          (Q.hessianApply D.rates unitState (alternateRightKernel Q D.rates)
            (alternateRightKernel Q D.rates)) = 0 := by
        rw [hqchart, hpchart, dot_hessian_scale, hfoldUnit, mul_zero]
      have hcenterChart : ∀ i, Q.jacobianApply D.rates unitState hh i =
          -Q.hessianApply D.rates unitState (alternateRightKernel Q D.rates)
            (alternateRightKernel Q D.rates) i := by
        intro i
        rw [hqchart, jacobianApply_scale, hcenterUnit i, hessianApply_scale]
        ring
      have hzero := hcharts true true D.rates hh hv heqUnit hdetUnit hguardR hguardL
        hfoldChart hcenterChart
      have hscale := dot_hessian_scale Q D.rates D.leftKernel D.rightKernel
        D.centerCorrection mu lam (lam ^ 2)
      rw [← hpchart, ← hqchart] at hscale
      change dot (alternateLeftKernel Q D.rates)
        (Q.hessianApply D.rates unitState (alternateRightKernel Q D.rates) hh) = _
        at hscale
      have hzero' : dot (alternateLeftKernel Q D.rates)
          (Q.hessianApply D.rates unitState (alternateRightKernel Q D.rates) hh) = 0 := by
        simpa [chartLeftKernel, chartRightKernel] using hzero
      rw [hzero'] at hscale
      apply hcubicUnit
      apply (mul_eq_zero.mp hscale.symm).resolve_left
      exact mul_ne_zero (mul_ne_zero hmu hlam) (pow_ne_zero 2 hlam)

/-- Backward-compatible interface for the finite residual layer.  The former
per-network nonzero-Jacobian hypothesis is now recognized as redundant. -/
theorem fourChartCubicDegenerate_excludes_cusp {m : ℕ}
    (Q : SmallPlanarNetwork m)
    (_hJ : PositiveEquilibriumJacobianNonzero Q)
    (hcharts : FourChartCubicDegenerate Q) :
    ¬ AdmitsTransverseCusp Q :=
  fourChartCubicDegenerate_excludes_cusp_intrinsic Q hcharts

end SmallCusp
