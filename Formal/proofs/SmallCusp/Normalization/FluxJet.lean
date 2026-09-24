import proofs.SmallCusp.Source.SourceClasses

/-!
# Positive-state to equilibrium-flux jet normalization

The Jacobian trace is intentionally absent: positive diagonal state scaling
does not preserve it.  Determinant singularity, the fold contraction, center
equation, cubic contraction, and rate-unfolding rank do transport after scaling
right-kernel and center vectors coordinatewise.
-/

open scoped BigOperators

namespace SmallCusp

def unitState : Species → ℝ := fun _ => 1

def equilibriumFlux {m : ℕ} (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x : Species → ℝ) : Fin m → ℝ :=
  fun r => k r * Q.monomial r x

noncomputable def scaleVectorByState (x v : Species → ℝ) : Species → ℝ :=
  fun i => v i / x i

def scaleRateDirection {m : ℕ} (Q : SmallPlanarNetwork m)
    (x : Species → ℝ) (u : Fin m → ℝ) : Fin m → ℝ :=
  fun r => u r * Q.monomial r x

private theorem firstDerivative_flux_term {m : ℕ}
    (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x q : Species → ℝ) (hx : PositiveVector x)
    (r : Fin m) (j : Species) :
    equilibriumFlux Q k x r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.unitMultiIndex j) unitState *
          scaleVectorByState x q j =
      k r * Q.multiDerivativeMonomial r (SmallPlanarNetwork.unitMultiIndex j) x * q j := by
  have hx0 : x 0 ≠ 0 := ne_of_gt (hx 0)
  have hx1 : x 1 ≠ 0 := ne_of_gt (hx 1)
  fin_cases j
  · by_cases hA : Q.reactant r 0 = 0
    · simp [equilibriumFlux, SmallPlanarNetwork.monomial,
        SmallPlanarNetwork.multiDerivativeMonomial,
        SmallPlanarNetwork.unitMultiIndex, unitState, scaleVectorByState,
        Fin.prod_univ_two, hA]
    · obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hA
      simp [equilibriumFlux, SmallPlanarNetwork.monomial,
        SmallPlanarNetwork.multiDerivativeMonomial,
        SmallPlanarNetwork.unitMultiIndex, unitState, scaleVectorByState,
        Fin.prod_univ_two, pow_succ, ha]
      field_simp [hx0]
  · by_cases hB : Q.reactant r 1 = 0
    · simp [equilibriumFlux, SmallPlanarNetwork.monomial,
        SmallPlanarNetwork.multiDerivativeMonomial,
        SmallPlanarNetwork.unitMultiIndex, unitState, scaleVectorByState,
        Fin.prod_univ_two, hB]
    · obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hB
      simp [equilibriumFlux, SmallPlanarNetwork.monomial,
        SmallPlanarNetwork.multiDerivativeMonomial,
        SmallPlanarNetwork.unitMultiIndex, unitState, scaleVectorByState,
        Fin.prod_univ_two, pow_succ, hb]
      field_simp [hx1]

private theorem secondDerivative_flux_term {m : ℕ}
    (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x q h : Species → ℝ) (hx : PositiveVector x)
    (r : Fin m) (j l : Species) :
    equilibriumFlux Q k x r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.pairMultiIndex j l) unitState *
          scaleVectorByState x q j * scaleVectorByState x h l =
      k r * Q.multiDerivativeMonomial r (SmallPlanarNetwork.pairMultiIndex j l) x * q j * h l := by
  have hx0 : x 0 ≠ 0 := ne_of_gt (hx 0)
  have hx1 : x 1 ≠ 0 := ne_of_gt (hx 1)
  fin_cases j <;> fin_cases l
  · by_cases hA : Q.reactant r 0 < 2
    · have : Q.reactant r 0 = 0 ∨ Q.reactant r 0 = 1 := by omega
      rcases this with h | h <;>
        simp [equilibriumFlux, SmallPlanarNetwork.monomial,
          SmallPlanarNetwork.multiDerivativeMonomial,
          SmallPlanarNetwork.pairMultiIndex, unitState, scaleVectorByState,
          Fin.prod_univ_two, h]
    · obtain ⟨a, ha⟩ : ∃ a, Q.reactant r 0 = a + 2 := by
        use Q.reactant r 0 - 2
        omega
      simp [equilibriumFlux, SmallPlanarNetwork.monomial,
        SmallPlanarNetwork.multiDerivativeMonomial,
        SmallPlanarNetwork.pairMultiIndex, unitState, scaleVectorByState,
        Fin.prod_univ_two, Nat.descFactorial_succ, pow_succ, ha]
      field_simp [hx0]
  · by_cases hA : Q.reactant r 0 = 0
    · simp [equilibriumFlux, SmallPlanarNetwork.monomial,
        SmallPlanarNetwork.multiDerivativeMonomial,
        SmallPlanarNetwork.pairMultiIndex, unitState, scaleVectorByState,
        Fin.prod_univ_two, hA]
    · by_cases hB : Q.reactant r 1 = 0
      · simp [equilibriumFlux, SmallPlanarNetwork.monomial,
          SmallPlanarNetwork.multiDerivativeMonomial,
          SmallPlanarNetwork.pairMultiIndex, unitState, scaleVectorByState,
          Fin.prod_univ_two, hB]
      · obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hA
        obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hB
        simp [equilibriumFlux, SmallPlanarNetwork.monomial,
          SmallPlanarNetwork.multiDerivativeMonomial,
          SmallPlanarNetwork.pairMultiIndex, unitState, scaleVectorByState,
          Fin.prod_univ_two, pow_succ, ha, hb]
        field_simp [hx0, hx1]
  · by_cases hA : Q.reactant r 0 = 0
    · simp [equilibriumFlux, SmallPlanarNetwork.monomial,
        SmallPlanarNetwork.multiDerivativeMonomial,
        SmallPlanarNetwork.pairMultiIndex, unitState, scaleVectorByState,
        Fin.prod_univ_two, hA]
    · by_cases hB : Q.reactant r 1 = 0
      · simp [equilibriumFlux, SmallPlanarNetwork.monomial,
          SmallPlanarNetwork.multiDerivativeMonomial,
          SmallPlanarNetwork.pairMultiIndex, unitState, scaleVectorByState,
          Fin.prod_univ_two, hB]
      · obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hA
        obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hB
        simp [equilibriumFlux, SmallPlanarNetwork.monomial,
          SmallPlanarNetwork.multiDerivativeMonomial,
          SmallPlanarNetwork.pairMultiIndex, unitState, scaleVectorByState,
          Fin.prod_univ_two, pow_succ, ha, hb]
        field_simp [hx0, hx1]
  · by_cases hB : Q.reactant r 1 < 2
    · have : Q.reactant r 1 = 0 ∨ Q.reactant r 1 = 1 := by omega
      rcases this with h | h <;>
        simp [equilibriumFlux, SmallPlanarNetwork.monomial,
          SmallPlanarNetwork.multiDerivativeMonomial,
          SmallPlanarNetwork.pairMultiIndex, unitState, scaleVectorByState,
          Fin.prod_univ_two, h]
    · obtain ⟨b, hb⟩ : ∃ b, Q.reactant r 1 = b + 2 := by
        use Q.reactant r 1 - 2
        omega
      simp [equilibriumFlux, SmallPlanarNetwork.monomial,
        SmallPlanarNetwork.multiDerivativeMonomial,
        SmallPlanarNetwork.pairMultiIndex, unitState, scaleVectorByState,
        Fin.prod_univ_two, Nat.descFactorial_succ, pow_succ, hb]
      field_simp [hx1]

theorem massAction_equilibriumFlux {m : ℕ} (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x : Species → ℝ) (i : Species) :
    Q.massAction (equilibriumFlux Q k x) unitState i = Q.massAction k x i := by
  simp only [SmallPlanarNetwork.massAction]
  apply Finset.sum_congr rfl
  intro r _
  simp [equilibriumFlux, SmallPlanarNetwork.monomial, unitState, Fin.prod_univ_two]
  ring

private theorem jacobian_term_equilibriumFlux {m : ℕ} (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x q : Species → ℝ)
    (hx : PositiveVector x) (i j : Species) :
    Q.jacobian (equilibriumFlux Q k x) unitState i j * scaleVectorByState x q j =
      Q.jacobian k x i j * q j := by
  simp only [SmallPlanarNetwork.jacobian, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  calc
    ((Q.stoich i r : ℝ) * equilibriumFlux Q k x r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.unitMultiIndex j) unitState) *
        scaleVectorByState x q j =
      (Q.stoich i r : ℝ) *
        (equilibriumFlux Q k x r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.unitMultiIndex j) unitState *
          scaleVectorByState x q j) := by ring
    _ = (Q.stoich i r : ℝ) *
        (k r * Q.multiDerivativeMonomial r
          (SmallPlanarNetwork.unitMultiIndex j) x * q j) := by
      rw [firstDerivative_flux_term Q k x q hx r j]
    _ = ((Q.stoich i r : ℝ) * k r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.unitMultiIndex j) x) * q j := by
      ring

theorem jacobian_equilibriumFlux {m : ℕ} (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x : Species → ℝ) (hx : PositiveVector x)
    (i j : Species) :
    Q.jacobian (equilibriumFlux Q k x) unitState i j =
      Q.jacobian k x i j * x j := by
  have hterm := jacobian_term_equilibriumFlux Q k x (fun _ => 1) hx i j
  have hxj : x j ≠ 0 := ne_of_gt (hx j)
  simp only [scaleVectorByState, div_eq_mul_inv, mul_one] at hterm
  calc
    Q.jacobian (equilibriumFlux Q k x) unitState i j =
        (Q.jacobian (equilibriumFlux Q k x) unitState i j *
          (1 * (x j)⁻¹)) * x j := by field_simp
    _ = Q.jacobian k x i j * x j := by rw [hterm]

theorem jacobianApply_equilibriumFlux {m : ℕ} (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x q : Species → ℝ)
    (hx : PositiveVector x) (i : Species) :
    Q.jacobianApply (equilibriumFlux Q k x) unitState
        (scaleVectorByState x q) i =
      Q.jacobianApply k x q i := by
  simp only [SmallPlanarNetwork.jacobianApply]
  apply Finset.sum_congr rfl
  intro j _
  exact jacobian_term_equilibriumFlux Q k x q hx i j

private theorem hessian_term_equilibriumFlux {m : ℕ} (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x q h : Species → ℝ)
    (hx : PositiveVector x) (i j l : Species) :
    Q.hessian (equilibriumFlux Q k x) unitState i j l *
          scaleVectorByState x q j * scaleVectorByState x h l =
      Q.hessian k x i j l * q j * h l := by
  simp only [SmallPlanarNetwork.hessian, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  calc
    ((Q.stoich i r : ℝ) * equilibriumFlux Q k x r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.pairMultiIndex j l) unitState) *
          scaleVectorByState x q j * scaleVectorByState x h l =
      (Q.stoich i r : ℝ) *
        (equilibriumFlux Q k x r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.pairMultiIndex j l) unitState *
          scaleVectorByState x q j * scaleVectorByState x h l) := by ring
    _ = (Q.stoich i r : ℝ) *
        (k r * Q.multiDerivativeMonomial r
          (SmallPlanarNetwork.pairMultiIndex j l) x * q j * h l) := by
      rw [secondDerivative_flux_term Q k x q h hx r j l]
    _ = ((Q.stoich i r : ℝ) * k r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.pairMultiIndex j l) x) *
          q j * h l := by ring

theorem hessianApply_equilibriumFlux {m : ℕ} (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x q h : Species → ℝ)
    (hx : PositiveVector x) (i : Species) :
    Q.hessianApply (equilibriumFlux Q k x) unitState
        (scaleVectorByState x q) (scaleVectorByState x h) i =
      Q.hessianApply k x q h i := by
  simp only [SmallPlanarNetwork.hessianApply]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  exact hessian_term_equilibriumFlux Q k x q h hx i j l

theorem rateFieldVariation_scaled {m : ℕ} (Q : SmallPlanarNetwork m)
    (x : Species → ℝ) (u : Fin m → ℝ) (i : Species) :
    Q.rateFieldVariation (scaleRateDirection Q x u) unitState i =
      Q.rateFieldVariation u x i := by
  simp only [SmallPlanarNetwork.rateFieldVariation]
  apply Finset.sum_congr rfl
  intro r _
  simp [scaleRateDirection, SmallPlanarNetwork.monomial, unitState,
    Fin.prod_univ_two]
  ring

theorem rateJacobianVariation_scaled {m : ℕ} (Q : SmallPlanarNetwork m)
    (x q : Species → ℝ) (hx : PositiveVector x)
    (u : Fin m → ℝ) (i : Species) :
    Q.rateJacobianVariation (scaleRateDirection Q x u) unitState
        (scaleVectorByState x q) i =
      Q.rateJacobianVariation u x q i := by
  simp only [SmallPlanarNetwork.rateJacobianVariation]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  calc
    (Q.stoich i r : ℝ) * scaleRateDirection Q x u r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.unitMultiIndex j) unitState *
          scaleVectorByState x q j =
      (Q.stoich i r : ℝ) *
        (equilibriumFlux Q u x r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.unitMultiIndex j) unitState *
          scaleVectorByState x q j) := by
        simp [scaleRateDirection, equilibriumFlux]
        ring
    _ = (Q.stoich i r : ℝ) *
        (u r * Q.multiDerivativeMonomial r
          (SmallPlanarNetwork.unitMultiIndex j) x * q j) := by
      rw [firstDerivative_flux_term Q u x q hx r j]
    _ = (Q.stoich i r : ℝ) * u r *
          Q.multiDerivativeMonomial r (SmallPlanarNetwork.unitMultiIndex j) x * q j := by
      ring

end SmallCusp
