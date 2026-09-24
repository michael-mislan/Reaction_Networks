import proofs.OscillatoryCores.DeletionMinimality

namespace OscillatoryCores
open DUnstableCores
open scoped BigOperators

noncomputable def deletionWeight : Fin 5 → Fin 4 → ℝ :=
  ![![7/2, -1/4, 0, 1/2], ![-2, 2/3, 0, 1/2],
    ![7/2, -17/24, 11/12, -5/12], ![-2, -1/4, 0, 1/2],
    ![-2, 5/24, -11/12, -4/3]]

theorem deletionWeight_column (j l : Fin 5) (h : l ≠ j) :
    ∑ i, deletionWeight j i * (source.stoich i l : ℝ) = 1 := by
  fin_cases j <;> fin_cases l <;>
    norm_num [deletionWeight, source, SourceNetwork.stoich, Fin.sum_univ_succ] at *

theorem deletion_observable_velocity (j : Fin 5) (v : Fin 5 → ℝ) (hj : v j = 0) :
    ∑ i, deletionWeight j i * (∑ l, (source.stoich i l : ℝ) * v l) = ∑ l, v l := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_mul]
  by_cases h : l = j
  · simp [h, hj]
  · rw [deletionWeight_column j l h, one_mul]

theorem deletion_observable_hasDerivAt (k : Fin 5 → ℝ) (j : Fin 5)
    (hj : k j = 0) (x : ℝ → Fin 4 → ℝ) (hode : Solves k x) (t : ℝ) :
    HasDerivAt (fun s => ∑ i, deletionWeight j i * x s i)
      (∑ l, trajectoryFlux k x t l) t := by
  have h := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => (hode t i).const_mul (deletionWeight j i))
  rw [deletion_observable_velocity j _ (by simp [trajectoryFlux, hj])] at h
  exact h

theorem balanced_flux_inflow (v : Fin 5 → ℝ)
    (h : ∀ i, ∑ j, (source.stoich i j : ℝ) * v j = 0) :
    v = ![v 4, 3 * v 4 / 2, v 4, v 4, v 4] := by
  obtain ⟨h3,h1,h2,h4⟩ := kernel_coordinates v h
  funext j
  fin_cases j <;> simp <;> linarith

theorem periodic_integrated_flux (k : Fin 5 → ℝ) (x : ℝ → Fin 4 → ℝ)
    (hode : Solves k x) (T : ℝ) (hreturn : x T = x 0) :
    (fun j => ∫ t in (0 : ℝ)..T, trajectoryFlux k x t j) =
      ![T * k 4, 3 * (T * k 4) / 2, T * k 4, T * k 4, T * k 4] := by
  have hx (i : Fin 4) : Continuous (fun t => x t i) :=
    continuous_iff_continuousAt.mpr (fun t => (hode t i).continuousAt)
  have h := balanced_flux_inflow _ (integrated_flux_balanced
    (fun i j => (source.stoich i j : ℝ)) x (trajectoryFlux k x) T
    (trajectoryFlux_continuous k x hx) hode hreturn)
  have h5 : (∫ t in (0 : ℝ)..T, trajectoryFlux k x t 4) = T * k 4 := by
    simp [trajectoryFlux, massActionMonomial, source, Fin.prod_univ_succ]
  simpa only [h5] using h

end OscillatoryCores
