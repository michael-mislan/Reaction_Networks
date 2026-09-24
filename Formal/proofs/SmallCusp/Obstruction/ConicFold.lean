import proofs.SmallCusp.Obstruction.ConicDeterminant

/-!
# Canonical quadratic-fold obstruction

For a singular two-dimensional Jacobian, `(b,-a)` is a canonical right
kernel vector and `(c,-a)` a canonical left kernel vector.  Any nonzero
kernel pair is proportional to these vectors, so cusp fold degeneracy forces
the canonical quartic fold polynomial to vanish.
-/

namespace SmallCusp

def canonicalRightKernel {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) : Species → ℝ := ![
  Q.jacobian v unitState 0 1,
  -Q.jacobian v unitState 0 0
]

def canonicalLeftKernel {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) : Species → ℝ := ![
  Q.jacobian v unitState 1 0,
  -Q.jacobian v unitState 0 0
]

def canonicalFold {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) : ℝ :=
  dot (canonicalLeftKernel Q v)
    (Q.hessianApply v unitState (canonicalRightKernel Q v)
      (canonicalRightKernel Q v))

private theorem fold_scale {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) (p q : Species → ℝ) (mu lam : ℝ) :
    dot (fun i ↦ mu * p i)
        (Q.hessianApply v unitState (fun i ↦ lam * q i)
          (fun i ↦ lam * q i)) =
      mu * lam ^ 2 * dot p (Q.hessianApply v unitState q q) := by
  simp [dot, SmallPlanarNetwork.hessianApply, Fin.sum_univ_two]
  ring

theorem canonicalFold_eq_zero_of_normalized_fold {m : ℕ}
    (Q : SmallPlanarNetwork m) (v : Fin m → ℝ)
    (q p : Species → ℝ)
    (hright : ∀ i, Q.jacobianApply v unitState q i = 0)
    (hleft : ∀ j, ∑ i : Species, p i * Q.jacobian v unitState i j = 0)
    (hq : q ≠ 0) (hp : p ≠ 0)
    (hfold : dot p (Q.hessianApply v unitState q q) = 0) :
    canonicalFold Q v = 0 := by
  have hr0 := hright 0
  have hl0 := hleft 0
  simp only [SmallPlanarNetwork.jacobianApply, Fin.sum_univ_two] at hr0
  simp only [Fin.sum_univ_two] at hl0
  have hqcomp : q 0 ≠ 0 ∨ (q 0 = 0 ∧ q 1 ≠ 0) := by
    by_cases h0 : q 0 = 0
    · right
      refine ⟨h0, ?_⟩
      intro h1
      apply hq
      funext i
      fin_cases i <;> assumption
    · exact Or.inl h0
  have hpcomp : p 0 ≠ 0 ∨ (p 0 = 0 ∧ p 1 ≠ 0) := by
    by_cases h0 : p 0 = 0
    · right
      refine ⟨h0, ?_⟩
      intro h1
      apply hp
      funext i
      fin_cases i <;> assumption
    · exact Or.inl h0
  rcases hqcomp with hq0 | hq1
  · let lam := Q.jacobian v unitState 0 1 / q 0
    have hqcan : canonicalRightKernel Q v = fun i ↦ lam * q i := by
      funext i
      fin_cases i
      · simp [canonicalRightKernel, lam, hq0]
      · simp only [canonicalRightKernel]
        dsimp [lam]
        field_simp
        linarith
    rcases hpcomp with hp0 | ⟨hp0, hp1⟩
    · let mu := Q.jacobian v unitState 1 0 / p 0
      have hpcan : canonicalLeftKernel Q v = fun i ↦ mu * p i := by
        funext i
        fin_cases i
        · simp [canonicalLeftKernel, mu, hp0]
        · simp only [canonicalLeftKernel]
          dsimp [mu]
          field_simp
          linarith
      rw [canonicalFold, hqcan, hpcan, fold_scale, hfold, mul_zero]
    · have hc : Q.jacobian v unitState 1 0 = 0 := by
        rw [hp0, zero_mul, zero_add] at hl0
        exact (mul_eq_zero.mp hl0).resolve_left hp1
      let mu := -Q.jacobian v unitState 0 0 / p 1
      have hpcan : canonicalLeftKernel Q v = fun i ↦ mu * p i := by
        funext i
        fin_cases i
        · simp [canonicalLeftKernel, hp0, hc]
        · simp [canonicalLeftKernel, mu, hp1]
      rw [canonicalFold, hqcan, hpcan, fold_scale, hfold, mul_zero]
  · rcases hq1 with ⟨hq0, hq1⟩
    have hb : Q.jacobian v unitState 0 1 = 0 := by
      rw [hq0, mul_zero, zero_add] at hr0
      exact (mul_eq_zero.mp hr0).resolve_right hq1
    let lam := -Q.jacobian v unitState 0 0 / q 1
    have hqcan : canonicalRightKernel Q v = fun i ↦ lam * q i := by
      funext i
      fin_cases i
      · simp [canonicalRightKernel, hq0, hb]
      · simp [canonicalRightKernel, lam, hq1]
    rcases hpcomp with hp0 | ⟨hp0, hp1⟩
    · let mu := Q.jacobian v unitState 1 0 / p 0
      have hpcan : canonicalLeftKernel Q v = fun i ↦ mu * p i := by
        funext i
        fin_cases i
        · simp [canonicalLeftKernel, mu, hp0]
        · simp only [canonicalLeftKernel]
          dsimp [mu]
          field_simp
          linarith
      rw [canonicalFold, hqcan, hpcan, fold_scale, hfold, mul_zero]
    · have hc : Q.jacobian v unitState 1 0 = 0 := by
        rw [hp0, zero_mul, zero_add] at hl0
        exact (mul_eq_zero.mp hl0).resolve_left hp1
      let mu := -Q.jacobian v unitState 0 0 / p 1
      have hpcan : canonicalLeftKernel Q v = fun i ↦ mu * p i := by
        funext i
        fin_cases i
        · simp [canonicalLeftKernel, hp0, hc]
        · simp [canonicalLeftKernel, mu, hp1]
      rw [canonicalFold, hqcan, hpcan, fold_scale, hfold, mul_zero]

private theorem positive_quartic_sum {m : ℕ}
    (coeff : Fin m → Fin m → Fin m → Fin m → ℝ)
    (v : Fin m → ℝ)
    (hc : ∀ i j k l, 0 ≤ coeff i j k l) (hv : PositiveVector v)
    (hw : ∃ i j k l, 0 < coeff i j k l) :
    0 < ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, ∑ l : Fin m,
      coeff i j k l * v i * v j * v k * v l := by
  rcases hw with ⟨wi, wj, wk, wl, hw⟩
  have hterm : ∀ i j k l, 0 ≤ coeff i j k l * v i * v j * v k * v l := by
    intro i j k l
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (hc i j k l) (le_of_lt (hv i)))
          (le_of_lt (hv j)))
        (le_of_lt (hv k)))
      (le_of_lt (hv l))
  have h3 : ∀ i j k, 0 ≤ ∑ l : Fin m,
      coeff i j k l * v i * v j * v k * v l := by
    intro i j k
    exact Finset.sum_nonneg fun l _ ↦ hterm i j k l
  have h2 : ∀ i j, 0 ≤ ∑ k : Fin m, ∑ l : Fin m,
      coeff i j k l * v i * v j * v k * v l := by
    intro i j
    exact Finset.sum_nonneg fun k _ ↦ h3 i j k
  have h1 : ∀ i, 0 ≤ ∑ j : Fin m, ∑ k : Fin m, ∑ l : Fin m,
      coeff i j k l * v i * v j * v k * v l := by
    intro i
    exact Finset.sum_nonneg fun j _ ↦ h2 i j
  apply (Finset.sum_pos_iff_of_nonneg fun i _ ↦ h1 i).2
  refine ⟨wi, Finset.mem_univ _, ?_⟩
  apply (Finset.sum_pos_iff_of_nonneg fun j _ ↦ h2 wi j).2
  refine ⟨wj, Finset.mem_univ _, ?_⟩
  apply (Finset.sum_pos_iff_of_nonneg fun k _ ↦ h3 wi wj k).2
  refine ⟨wk, Finset.mem_univ _, ?_⟩
  apply (Finset.sum_pos_iff_of_nonneg fun l _ ↦ hterm wi wj wk l).2
  refine ⟨wl, Finset.mem_univ _, ?_⟩
  exact mul_pos (mul_pos (mul_pos (mul_pos hw (hv wi)) (hv wj)) (hv wk)) (hv wl)

theorem conicFoldCertificate_excludes_cusp {m : ℕ}
    (Q : SmallPlanarNetwork m) (sign : ℝ)
    (coeff : Fin m → Fin m → Fin m → Fin m → ℝ)
    (detMultiplier : Fin m → Fin m → ℝ)
    (eqMultiplier : Species → Fin m → Fin m → Fin m → ℝ)
    (hc : ∀ i j k l, 0 ≤ coeff i j k l)
    (hw : ∃ i j k l, 0 < coeff i j k l)
    (hidentity : ∀ v : Fin m → ℝ,
      sign * canonicalFold Q v =
        (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, ∑ l : Fin m,
          coeff i j k l * v i * v j * v k * v l) +
        (∑ i : Fin m, ∑ j : Fin m, detMultiplier i j * v i * v j) *
          unitJacobianDet Q v +
        ∑ s : Species,
          (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
            eqMultiplier s i j k * v i * v j * v k) *
            Q.massAction v unitState s) :
    ¬ AdmitsTransverseCusp Q := by
  intro hcusp
  obtain ⟨D, hD⟩ := admitsTransverseCusp_implies_traceFreeNormalized Q hcusp
  rcases hD with ⟨hstate, hv, heq, hright, hleft, hq, hp,
    hfold, _hcenter, _hcubic, _hunfold⟩
  have hcanonical : canonicalFold Q D.rates = 0 := by
    apply canonicalFold_eq_zero_of_normalized_fold Q D.rates
      D.rightKernel D.leftKernel
    · intro i
      simpa [hstate] using hright i
    · intro j
      simpa [hstate] using hleft j
    · exact hq
    · exact hp
    · simpa [hstate] using hfold
  have hdet : unitJacobianDet Q D.rates = 0 := by
    apply unitJacobianDet_eq_zero_of_rightKernel Q D.rates D.rightKernel hq
    intro i
    simpa [hstate] using hright i
  have hpositive := positive_quartic_sum coeff D.rates hc hv hw
  have hid := hidentity D.rates
  have heqUnit : ∀ s, Q.massAction D.rates unitState s = 0 := by
    intro s
    simpa [hstate] using heq s
  simp_rw [heqUnit, hdet, hcanonical, mul_zero, Finset.sum_const_zero,
    add_zero] at hid
  linarith

end SmallCusp
