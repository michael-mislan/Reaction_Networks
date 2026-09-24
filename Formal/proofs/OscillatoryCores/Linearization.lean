import proofs.OscillatoryCores.Source
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace OscillatoryCores

open DUnstableCores
open scoped BigOperators

abbrev State := Fin 4 → ℝ

noncomputable def monomialLinear (j : Fin 5) : State →L[ℝ] ℝ :=
  ∑ i : Fin 4, (source.reactant i j : ℝ) • ContinuousLinearMap.proj i

theorem monomial_hasFDerivAt_one (j : Fin 5) :
    HasFDerivAt (fun z : State => massActionMonomial source z j)
      (monomialLinear j) (fun _ => 1) := by
  have hp (i : Fin 4) : HasFDerivAt (𝕜 := ℝ) (fun z : State => z i ^ source.reactant i j)
      ((source.reactant i j : ℝ) • ContinuousLinearMap.proj i) (fun _ => 1) := by
    simpa using (hasFDerivAt_apply (𝕜 := ℝ) i (fun _ : Fin 4 => (1 : ℝ))).pow
      (source.reactant i j)
  simpa [massActionMonomial, monomialLinear] using
    HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hp i)

noncomputable def normalizedCoefficient (t : ℝ) (i : Fin 4) (j : Fin 5) : ℝ :=
  (source.stoich i j : ℝ) * flux j / equilibrium t i

noncomputable def normalizedField (t : ℝ) (z : State) : State :=
  fun i => ∑ j, normalizedCoefficient t i j * massActionMonomial source z j

noncomputable def normalizedLinear (t : ℝ) : State →L[ℝ] State :=
  ContinuousLinearMap.pi (fun i => ∑ j, normalizedCoefficient t i j • monomialLinear j)

theorem normalizedField_hasFDerivAt_one (t : ℝ) :
    HasFDerivAt (normalizedField t) (normalizedLinear t) (fun _ => 1) := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact HasFDerivAt.fun_sum (fun j _ =>
    (monomial_hasFDerivAt_one j).const_mul (normalizedCoefficient t i j))

theorem monomial_mul (x z : State) (j : Fin 5) :
    massActionMonomial source (fun i => x i * z i) j =
      massActionMonomial source x j * massActionMonomial source z j := by
  simp [massActionMonomial, mul_pow, Finset.prod_mul_distrib]

/-- The normalization is exactly conjugate to the literal mass-action ODE. -/
theorem normalization_source {t : ℝ} (ht : 0 < t) (z : State) (i : Fin 4) :
    equilibrium t i * normalizedField t z i =
      ∑ j, (source.stoich i j : ℝ) *
        (rates t j * massActionMonomial source (fun k => equilibrium t k * z k) j) := by
  unfold normalizedField
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [monomial_mul]
  have hf := equilibrium_flux ht j
  have he : equilibrium t i ≠ 0 := ne_of_gt (equilibrium_pos ht i)
  unfold normalizedCoefficient
  rw [← mul_assoc (rates t j), hf]
  field_simp [he]

end OscillatoryCores
