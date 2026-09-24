import proofs.SmallCusp.Obstruction.CircuitFold
import proofs.SmallCusp.Obstruction.RationalCircuitChecker

/-!
# Exact fold obstruction for three rational equilibrium generators

This module factors the end-to-end mechanism tested by `CircuitFoldPilot`.
The continuum is covered by the proved rational circuit convex hull; a finite
certificate supplies only an exact three-generator list and a local polynomial
identity.
-/

open scoped BigOperators

namespace SmallCusp

def rationalGeneratorReal {g : ℕ} (generator : Fin g → Fin 5 → ℚ) :
    Fin g → Fin 5 → ℝ := fun a ↦ rationalFluxReal (generator a)

theorem rationalGeneratorReal_injective
    {g : ℕ} (generator : Fin g → Fin 5 → ℚ)
    (hgenerator : Function.Injective generator) :
    Function.Injective (rationalGeneratorReal generator) := by
  intro a b h
  apply hgenerator
  funext r
  have hr := congrFun h r
  change (generator a r : ℝ) = (generator b r : ℝ) at hr
  exact_mod_cast hr

theorem threeRationalCircuitGenerator_nonnegative
    (C : CodedBimolNetwork) (generator : Fin 3 → Fin 5 → ℚ)
    (hcircuits : rationalCircuitFinset C = Finset.univ.image generator)
    (a : Fin 3) (r : Fin 5) :
    0 ≤ rationalGeneratorReal generator a r := by
  have hmem : generator a ∈ rationalCircuitFinset C := by
    rw [hcircuits]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hq := (rationalCircuitFinset_valid C hmem).1 r
  change 0 ≤ (generator a r : ℝ)
  exact_mod_cast hq

theorem rationalCircuitGenerator_nonnegative {g : ℕ}
    (C : CodedBimolNetwork) (generator : Fin g → Fin 5 → ℚ)
    (hcircuits : rationalCircuitFinset C = Finset.univ.image generator)
    (a : Fin g) (r : Fin 5) :
    0 ≤ rationalGeneratorReal generator a r := by
  have hmem : generator a ∈ rationalCircuitFinset C := by
    rw [hcircuits]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hq := (rationalCircuitFinset_valid C hmem).1 r
  change 0 ≤ (generator a r : ℝ)
  exact_mod_cast hq

/-- The exact rational circuit list generates the entire positive equilibrium
cone.  This is the generator mechanism used by all finite fold certificates;
the finite data never enumerate equilibrium outputs. -/
theorem rationalCircuit_represent {g : ℕ}
    (C : CodedBimolNetwork) (generator : Fin g → Fin 5 → ℚ)
    (hcircuits : rationalCircuitFinset C = Finset.univ.image generator)
    (hgenerator : Function.Injective generator)
    (v : Fin 5 → ℝ) (hv : PositiveVector v)
    (heq : ∀ s : Species, C.toNetwork.massAction v unitState s = 0) :
    ∃ t : Fin g → ℝ,
      NonnegativeVector t ∧
        circuitCombination (rationalGeneratorReal generator) t = v := by
  classical
  let total : ℝ := ∑ r, v r
  have htotal : 0 < total :=
    Finset.sum_pos (fun r _ ↦ hv r) Finset.univ_nonempty
  have hx := positiveEquilibrium_normalized_mem C v hv heq
  have hxconv : normalizeRealFlux v ∈ convexHull ℝ
      (rationalFluxReal '' (rationalCircuitFinset C : Set (Fin 5 → ℚ))) := by
    rw [← normalizedEquilibriumFiber_eq_convexHull_rationalCircuits C]
    exact hx
  let s : Finset (Fin 5 → ℝ) :=
    (Finset.univ : Finset (Fin g)).image (rationalGeneratorReal generator)
  have hsset : (s : Set (Fin 5 → ℝ)) =
      rationalFluxReal '' (rationalCircuitFinset C : Set (Fin 5 → ℚ)) := by
    ext y
    simp [s, hcircuits, rationalGeneratorReal]
  have hxs : normalizeRealFlux v ∈ convexHull ℝ (s : Set (Fin 5 → ℝ)) := by
    rw [hsset]
    exact hxconv
  obtain ⟨w, hw, _hwsum, hwcenter⟩ := (Finset.mem_convexHull').mp hxs
  have hrealinj : Function.Injective (rationalGeneratorReal generator) :=
    rationalGeneratorReal_injective generator hgenerator
  have hwcenter' :
      ∑ a : Fin g, w (rationalGeneratorReal generator a) •
          rationalGeneratorReal generator a = normalizeRealFlux v := by
    rw [show s = Finset.univ.image (rationalGeneratorReal generator) by rfl]
      at hwcenter
    rw [Finset.sum_image] at hwcenter
    · exact hwcenter
    · intro a _ b _ hab
      exact hrealinj hab
  let t : Fin g → ℝ := fun a ↦ total * w (rationalGeneratorReal generator a)
  refine ⟨t, ?_, ?_⟩
  · intro a
    exact mul_nonneg htotal.le (hw _ (by simp [s]))
  · funext r
    have hcoord := congrFun hwcenter' r
    have hcoord' :
        ∑ a, w (rationalGeneratorReal generator a) *
            rationalGeneratorReal generator a r = normalizeRealFlux v r := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcoord
    change ∑ a, t a * rationalGeneratorReal generator a r = v r
    calc
      ∑ a, t a * rationalGeneratorReal generator a r =
          total * ∑ a, w (rationalGeneratorReal generator a) *
            rationalGeneratorReal generator a r := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        simp [t]
        ring
      _ = total * normalizeRealFlux v r := by rw [hcoord']
      _ = v r := by simp [normalizeRealFlux, total, htotal.ne']

/-- If the exact circuit finset consists of three distinct rational
generators, every full-support equilibrium is a nonnegative combination of
those generators. -/
theorem threeRationalCircuit_represent
    (C : CodedBimolNetwork) (generator : Fin 3 → Fin 5 → ℚ)
    (hcircuits : rationalCircuitFinset C = Finset.univ.image generator)
    (hgenerator : Function.Injective generator)
    (v : Fin 5 → ℝ) (hv : PositiveVector v)
    (heq : ∀ s : Species, C.toNetwork.massAction v unitState s = 0) :
    ∃ t : Fin 3 → ℝ,
      NonnegativeVector t ∧
        circuitCombination (rationalGeneratorReal generator) t = v := by
  classical
  let total : ℝ := ∑ r, v r
  have htotal : 0 < total :=
    Finset.sum_pos (fun r _ ↦ hv r) Finset.univ_nonempty
  have hx := positiveEquilibrium_normalized_mem C v hv heq
  have hxconv : normalizeRealFlux v ∈ convexHull ℝ
      (rationalFluxReal '' (rationalCircuitFinset C : Set (Fin 5 → ℚ))) := by
    rw [← normalizedEquilibriumFiber_eq_convexHull_rationalCircuits C]
    exact hx
  let s : Finset (Fin 5 → ℝ) :=
    (Finset.univ : Finset (Fin 3)).image (rationalGeneratorReal generator)
  have hsset : (s : Set (Fin 5 → ℝ)) =
      rationalFluxReal '' (rationalCircuitFinset C : Set (Fin 5 → ℚ)) := by
    ext y
    simp [s, hcircuits, rationalGeneratorReal]
  have hxs : normalizeRealFlux v ∈ convexHull ℝ (s : Set (Fin 5 → ℝ)) := by
    rw [hsset]
    exact hxconv
  obtain ⟨w, hw, _hwsum, hwcenter⟩ := (Finset.mem_convexHull').mp hxs
  have hrealinj : Function.Injective (rationalGeneratorReal generator) :=
    rationalGeneratorReal_injective generator hgenerator
  have hwcenter' :
      ∑ a : Fin 3, w (rationalGeneratorReal generator a) •
          rationalGeneratorReal generator a = normalizeRealFlux v := by
    rw [show s = Finset.univ.image (rationalGeneratorReal generator) by rfl]
      at hwcenter
    rw [Finset.sum_image] at hwcenter
    · exact hwcenter
    · intro a _ b _ hab
      exact hrealinj hab
  let t : Fin 3 → ℝ := fun a ↦ total * w (rationalGeneratorReal generator a)
  refine ⟨t, ?_, ?_⟩
  · intro a
    exact mul_nonneg htotal.le (hw _ (by simp [s]))
  · funext r
    have hcoord := congrFun hwcenter' r
    have hcoord' :
        ∑ a, w (rationalGeneratorReal generator a) *
            rationalGeneratorReal generator a r = normalizeRealFlux v r := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcoord
    change ∑ a, t a * rationalGeneratorReal generator a r = v r
    calc
      ∑ a, t a * rationalGeneratorReal generator a r =
          total * ∑ a, w (rationalGeneratorReal generator a) *
            rationalGeneratorReal generator a r := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        simp [t]
        ring
      _ = total * normalizeRealFlux v r := by rw [hcoord']
      _ = v r := by simp [normalizeRealFlux, total, htotal.ne']

/-- Reusable exact certificate theorem for a network whose normalized
equilibrium polytope has exactly three rational circuit generators. -/
theorem threeRationalCircuitFoldCertificate_excludes_cusp
    (C : CodedBimolNetwork) (generator : Fin 3 → Fin 5 → ℚ)
    (sign : ℝ)
    (residueCoeff : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (detMultiplier : Fin 3 → Fin 3 → ℝ)
    (hcircuits : rationalCircuitFinset C = Finset.univ.image generator)
    (hgenerator : Function.Injective generator)
    (hcoeff : ∀ a b c d, 0 ≤ residueCoeff a b c d)
    (hstrictSupport : ∀ active : Finset (Fin 3),
      (∀ r : Fin 5, ∃ a ∈ active,
        0 < rationalGeneratorReal generator a r) →
      ∃ a ∈ active, ∃ b ∈ active, ∃ c ∈ active, ∃ d ∈ active,
        0 < residueCoeff a b c d)
    (hidentity : ∀ t : Fin 3 → ℝ,
      sign * canonicalFold C.toNetwork
          (circuitCombination (rationalGeneratorReal generator) t) =
        circuitQuartic residueCoeff t +
          circuitQuadratic detMultiplier t *
            unitJacobianDet C.toNetwork
              (circuitCombination (rationalGeneratorReal generator) t)) :
    ¬ AdmitsTransverseCusp C.toNetwork := by
  apply supportCoverCircuitFoldCertificates_exclude_cusp C.toNetwork
    (fun _ : Unit ↦ sign)
    (fun _ ↦ rationalGeneratorReal generator)
    (fun _ ↦ residueCoeff)
    (fun _ ↦ detMultiplier)
  · intro v hv heq
    obtain ⟨t, ht, hv⟩ :=
      threeRationalCircuit_represent C generator hcircuits hgenerator v hv heq
    exact ⟨(), t, ht, hv⟩
  · intro _
    exact threeRationalCircuitGenerator_nonnegative C generator hcircuits
  · intro _
    exact hcoeff
  · intro _
    exact hstrictSupport
  · intro _
    exact hidentity

/-- Rational-data wrapper.  All order and support obligations are finite
decidable propositions over `ℚ`; only the final polynomial identity is stated
after casting to `ℝ`. -/
theorem threeRationalCircuitFoldCertificate_excludes_cusp_of_rational
    (C : CodedBimolNetwork) (generator : Fin 3 → Fin 5 → ℚ)
    (sign : ℚ)
    (residueCoeff : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℚ)
    (detMultiplier : Fin 3 → Fin 3 → ℚ)
    (hcircuits : rationalCircuitFinset C = Finset.univ.image generator)
    (hgenerator : Function.Injective generator)
    (hcoeff : ∀ a b c d, 0 ≤ residueCoeff a b c d)
    (hstrictSupport : ∀ active : Finset (Fin 3),
      (∀ r : Fin 5, ∃ a ∈ active, 0 < generator a r) →
      ∃ a ∈ active, ∃ b ∈ active, ∃ c ∈ active, ∃ d ∈ active,
        0 < residueCoeff a b c d)
    (hidentity : ∀ t : Fin 3 → ℝ,
      (sign : ℝ) * canonicalFold C.toNetwork
          (circuitCombination (rationalGeneratorReal generator) t) =
        circuitQuartic (fun a b c d ↦ (residueCoeff a b c d : ℝ)) t +
          circuitQuadratic (fun a b ↦ (detMultiplier a b : ℝ)) t *
            unitJacobianDet C.toNetwork
              (circuitCombination (rationalGeneratorReal generator) t)) :
    ¬ AdmitsTransverseCusp C.toNetwork := by
  apply threeRationalCircuitFoldCertificate_excludes_cusp C generator
    (sign : ℝ)
    (fun a b c d ↦ (residueCoeff a b c d : ℝ))
    (fun a b ↦ (detMultiplier a b : ℝ))
    hcircuits hgenerator
  · intro a b c d
    exact_mod_cast hcoeff a b c d
  · intro active hcover
    have hcoverRat : ∀ r : Fin 5, ∃ a ∈ active, 0 < generator a r := by
      intro r
      obtain ⟨a, ha, hpos⟩ := hcover r
      refine ⟨a, ha, ?_⟩
      change 0 < (generator a r : ℝ) at hpos
      exact_mod_cast hpos
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hpos⟩ :=
      hstrictSupport active hcoverRat
    refine ⟨a, ha, b, hb, c, hc, d, hd, ?_⟩
    exact_mod_cast hpos
  · exact hidentity

/-- Full-generator version of the rational fold certificate.  Unlike a
triangulated certificate, this theorem uses the complete rational circuit
cone at once, so no Caratheodory selection or enumeration of equilibrium
outputs is involved. -/
theorem rationalCircuitFoldCertificate_excludes_cusp_of_rational {g : ℕ}
    (C : CodedBimolNetwork) (generator : Fin g → Fin 5 → ℚ)
    (sign : ℚ)
    (residueCoeff : Fin g → Fin g → Fin g → Fin g → ℚ)
    (detMultiplier : Fin g → Fin g → ℚ)
    (hcircuits : rationalCircuitFinset C = Finset.univ.image generator)
    (hgenerator : Function.Injective generator)
    (hcoeff : ∀ a b c d, 0 ≤ residueCoeff a b c d)
    (hstrictSupport : ∀ active : Finset (Fin g),
      (∀ r : Fin 5, ∃ a ∈ active, 0 < generator a r) →
      ∃ a ∈ active, ∃ b ∈ active, ∃ c ∈ active, ∃ d ∈ active,
        0 < residueCoeff a b c d)
    (hidentity : ∀ t : Fin g → ℝ,
      (sign : ℝ) * canonicalFold C.toNetwork
          (circuitCombination (rationalGeneratorReal generator) t) =
        circuitQuartic (fun a b c d ↦ (residueCoeff a b c d : ℝ)) t +
          circuitQuadratic (fun a b ↦ (detMultiplier a b : ℝ)) t *
            unitJacobianDet C.toNetwork
              (circuitCombination (rationalGeneratorReal generator) t)) :
    ¬ AdmitsTransverseCusp C.toNetwork := by
  apply supportCoverCircuitFoldCertificates_exclude_cusp C.toNetwork
    (fun _ : Unit ↦ (sign : ℝ))
    (fun _ ↦ rationalGeneratorReal generator)
    (fun _ a b c d ↦ (residueCoeff a b c d : ℝ))
    (fun _ a b ↦ (detMultiplier a b : ℝ))
  · intro v hv heq
    obtain ⟨t, ht, hv⟩ :=
      rationalCircuit_represent C generator hcircuits hgenerator v hv heq
    exact ⟨(), t, ht, hv⟩
  · intro _ a r
    exact rationalCircuitGenerator_nonnegative C generator hcircuits a r
  · intro _ a b c d
    exact_mod_cast hcoeff a b c d
  · intro _ active hcover
    have hcoverRat : ∀ r : Fin 5, ∃ a ∈ active, 0 < generator a r := by
      intro r
      obtain ⟨a, ha, hpos⟩ := hcover r
      refine ⟨a, ha, ?_⟩
      change 0 < (generator a r : ℝ) at hpos
      exact_mod_cast hpos
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hpos⟩ :=
      hstrictSupport active hcoverRat
    refine ⟨a, ha, b, hb, c, hc, d, hd, ?_⟩
    exact_mod_cast hpos
  · intro _ t
    exact hidentity t

end SmallCusp
