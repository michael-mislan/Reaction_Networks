import proofs.SmallCusp.Obstruction.ConicFold

/-!
# Fold obstructions generated in equilibrium-circuit coordinates

The ambient quartic certificate has 85 multiplier coefficients because it
must also eliminate the two equilibrium equations.  Positive equilibrium
circuits generate that kernel intrinsically.  On a three-circuit cone only a
six-coefficient quadratic multiplier of the determinant remains.

This theorem isolates that mechanism.  A later finite checker supplies the
exact circuit cones, their coverage, and the pulled-back rational identities.
-/

open scoped BigOperators

namespace SmallCusp

def circuitCombination {g m : ℕ}
    (generator : Fin g → Fin m → ℝ) (t : Fin g → ℝ) : Fin m → ℝ :=
  fun r => ∑ a : Fin g, t a * generator a r

def circuitQuadratic {g : ℕ}
    (coeff : Fin g → Fin g → ℝ) (t : Fin g → ℝ) : ℝ :=
  ∑ a : Fin g, ∑ b : Fin g, coeff a b * t a * t b

def circuitQuartic {g : ℕ}
    (coeff : Fin g → Fin g → Fin g → Fin g → ℝ)
    (t : Fin g → ℝ) : ℝ :=
  ∑ a : Fin g, ∑ b : Fin g, ∑ c : Fin g, ∑ d : Fin g,
    coeff a b c d * t a * t b * t c * t d

/-- A circuit-local fold certificate excludes a transverse cusp.

`hrepresent` is the generator statement: every positive equilibrium flux is
represented in a certified circuit cone, with a strictly positive residual.
`hidentity` is only a ternary quartic identity modulo the pulled-back
determinant.  No ambient equilibrium multipliers or per-network analytic
arguments remain. -/
theorem circuitFoldCertificate_excludes_cusp {m g : ℕ}
    (Q : SmallPlanarNetwork m) (sign : ℝ)
    (generator : Fin g → Fin m → ℝ)
    (residueCoeff : Fin g → Fin g → Fin g → Fin g → ℝ)
    (detMultiplier : Fin g → Fin g → ℝ)
    (hrepresent : ∀ v : Fin m → ℝ,
      PositiveVector v →
      (∀ s : Species, Q.massAction v unitState s = 0) →
      ∃ t : Fin g → ℝ,
        NonnegativeVector t ∧
        circuitCombination generator t = v ∧
        0 < circuitQuartic residueCoeff t)
    (hidentity : ∀ t : Fin g → ℝ,
      sign * canonicalFold Q (circuitCombination generator t) =
        circuitQuartic residueCoeff t +
          circuitQuadratic detMultiplier t *
            unitJacobianDet Q (circuitCombination generator t)) :
    ¬ AdmitsTransverseCusp Q := by
  intro hcusp
  obtain ⟨D, hD⟩ := admitsTransverseCusp_implies_traceFreeNormalized Q hcusp
  rcases hD with ⟨hstate, hv, heq, hright, hleft, hq, hp,
    hfold, _hcenter, _hcubic, _hunfold⟩
  have heqUnit : ∀ s, Q.massAction D.rates unitState s = 0 := by
    intro s
    simpa [hstate] using heq s
  obtain ⟨t, _ht, hcomb, hpositive⟩ := hrepresent D.rates hv heqUnit
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
  have hid := hidentity t
  rw [hcomb, hcanonical, hdet] at hid
  simp only [mul_zero, add_zero] at hid
  linarith

/-- A family of local circuit-cone certificates excludes a transverse cusp.

The generator theorem chooses a cone `k` for each positive equilibrium flux.
The local certificate need only be strictly positive when its nonnegative
combination has full support.  This is the precise interface certified by the
finite three-circuit computations: boundary coordinates may vanish, provided
the resulting flux still uses every reaction. -/
theorem localCircuitFoldCertificates_exclude_cusp {m g : ℕ} {κ : Type*}
    (Q : SmallPlanarNetwork m) (sign : κ → ℝ)
    (generator : κ → Fin g → Fin m → ℝ)
    (residueCoeff : κ → Fin g → Fin g → Fin g → Fin g → ℝ)
    (detMultiplier : κ → Fin g → Fin g → ℝ)
    (hrepresent : ∀ v : Fin m → ℝ,
      PositiveVector v →
      (∀ s : Species, Q.massAction v unitState s = 0) →
      ∃ (k : κ) (t : Fin g → ℝ),
        NonnegativeVector t ∧ circuitCombination (generator k) t = v)
    (hpositive : ∀ (k : κ) (t : Fin g → ℝ),
      NonnegativeVector t →
      PositiveVector (circuitCombination (generator k) t) →
      0 < circuitQuartic (residueCoeff k) t)
    (hidentity : ∀ (k : κ) (t : Fin g → ℝ),
      sign k * canonicalFold Q (circuitCombination (generator k) t) =
        circuitQuartic (residueCoeff k) t +
          circuitQuadratic (detMultiplier k) t *
            unitJacobianDet Q (circuitCombination (generator k) t)) :
    ¬ AdmitsTransverseCusp Q := by
  intro hcusp
  obtain ⟨D, hD⟩ := admitsTransverseCusp_implies_traceFreeNormalized Q hcusp
  rcases hD with ⟨hstate, hv, heq, hright, hleft, hq, hp,
    hfold, _hcenter, _hcubic, _hunfold⟩
  have heqUnit : ∀ s, Q.massAction D.rates unitState s = 0 := by
    intro s
    simpa [hstate] using heq s
  obtain ⟨k, t, ht, hcomb⟩ := hrepresent D.rates hv heqUnit
  have hresidue : 0 < circuitQuartic (residueCoeff k) t := by
    apply hpositive k t ht
    simpa [hcomb] using hv
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
  have hid := hidentity k t
  rw [hcomb, hcanonical, hdet] at hid
  simp only [mul_zero, add_zero] at hid
  linarith

theorem circuitQuartic_pos_of_nonnegative_of_witness {g : ℕ}
    (coeff : Fin g → Fin g → Fin g → Fin g → ℝ)
    (t : Fin g → ℝ)
    (hc : ∀ a b c d, 0 ≤ coeff a b c d)
    (ht : NonnegativeVector t)
    {a b c d : Fin g} (hw : 0 < coeff a b c d)
    (ha : 0 < t a) (hb : 0 < t b) (hc' : 0 < t c) (hd : 0 < t d) :
    0 < circuitQuartic coeff t := by
  let term := fun a b c d ↦ coeff a b c d * t a * t b * t c * t d
  have hterm : ∀ i j k l, 0 ≤ term i j k l := by
    intro i j k l
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (hc i j k l) (ht i)) (ht j)) (ht k))
      (ht l)
  have h3 : ∀ i j k, 0 ≤ ∑ l, term i j k l := fun i j k ↦
    Finset.sum_nonneg fun l _ ↦ hterm i j k l
  have h2 : ∀ i j, 0 ≤ ∑ k, ∑ l, term i j k l := fun i j ↦
    Finset.sum_nonneg fun k _ ↦ h3 i j k
  have h1 : ∀ i, 0 ≤ ∑ j, ∑ k, ∑ l, term i j k l := fun i ↦
    Finset.sum_nonneg fun j _ ↦ h2 i j
  apply (Finset.sum_pos_iff_of_nonneg fun i _ ↦ h1 i).2
  refine ⟨a, Finset.mem_univ _, ?_⟩
  apply (Finset.sum_pos_iff_of_nonneg fun j _ ↦ h2 a j).2
  refine ⟨b, Finset.mem_univ _, ?_⟩
  apply (Finset.sum_pos_iff_of_nonneg fun k _ ↦ h3 a b k).2
  refine ⟨c, Finset.mem_univ _, ?_⟩
  apply (Finset.sum_pos_iff_of_nonneg fun l _ ↦ hterm a b c l).2
  refine ⟨d, Finset.mem_univ _, ?_⟩
  exact mul_pos (mul_pos (mul_pos (mul_pos hw ha) hb) hc') hd

/-- Finite support-cover form of the local circuit obstruction.  The strict
condition ranges only over subsets of the finite generator index type, so it
is directly reflectable by a Boolean checker. -/
theorem supportCoverCircuitFoldCertificates_exclude_cusp {m g : ℕ} {κ : Type*}
    (Q : SmallPlanarNetwork m) (sign : κ → ℝ)
    (generator : κ → Fin g → Fin m → ℝ)
    (residueCoeff : κ → Fin g → Fin g → Fin g → Fin g → ℝ)
    (detMultiplier : κ → Fin g → Fin g → ℝ)
    (hrepresent : ∀ v : Fin m → ℝ,
      PositiveVector v →
      (∀ s : Species, Q.massAction v unitState s = 0) →
      ∃ (k : κ) (t : Fin g → ℝ),
        NonnegativeVector t ∧ circuitCombination (generator k) t = v)
    (hgenerator : ∀ k a r, 0 ≤ generator k a r)
    (hcoeff : ∀ k a b c d, 0 ≤ residueCoeff k a b c d)
    (hstrictSupport : ∀ (k : κ) (active : Finset (Fin g)),
      (∀ r : Fin m, ∃ a ∈ active, 0 < generator k a r) →
      ∃ a ∈ active, ∃ b ∈ active, ∃ c ∈ active, ∃ d ∈ active,
        0 < residueCoeff k a b c d)
    (hidentity : ∀ (k : κ) (t : Fin g → ℝ),
      sign k * canonicalFold Q (circuitCombination (generator k) t) =
        circuitQuartic (residueCoeff k) t +
          circuitQuadratic (detMultiplier k) t *
            unitJacobianDet Q (circuitCombination (generator k) t)) :
    ¬ AdmitsTransverseCusp Q := by
  apply localCircuitFoldCertificates_exclude_cusp Q sign generator residueCoeff
    detMultiplier hrepresent
  · intro k t ht hv
    let active : Finset (Fin g) := Finset.univ.filter fun a ↦ 0 < t a
    have hcover : ∀ r : Fin m, ∃ a ∈ active, 0 < generator k a r := by
      intro r
      have hsum : 0 < ∑ a, t a * generator k a r := by
        simpa [circuitCombination] using hv r
      have hnonneg : ∀ a ∈ (Finset.univ : Finset (Fin g)),
          0 ≤ t a * generator k a r := by
        intro a _
        exact mul_nonneg (ht a) (hgenerator k a r)
      obtain ⟨a, _, ha⟩ := (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsum
      have hta : 0 < t a := lt_of_not_ge fun h ↦ by
        have : t a = 0 := le_antisymm h (ht a)
        simp [this] at ha
      have hga : 0 < generator k a r := lt_of_not_ge fun h ↦ by
        have : generator k a r = 0 := le_antisymm h (hgenerator k a r)
        simp [this] at ha
      exact ⟨a, by simp [active, hta], hga⟩
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hw⟩ :=
      hstrictSupport k active hcover
    apply circuitQuartic_pos_of_nonnegative_of_witness
      (residueCoeff k) t (hcoeff k) ht hw
    · simpa [active] using ha
    · simpa [active] using hb
    · simpa [active] using hc
    · simpa [active] using hd
  · exact hidentity

end SmallCusp
