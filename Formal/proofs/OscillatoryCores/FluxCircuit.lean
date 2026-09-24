import proofs.OscillatoryCores.Source

namespace OscillatoryCores

open DUnstableCores
open scoped BigOperators

theorem kernel_coordinates (u : Fin 5 → ℝ)
    (hu : ∀ i, ∑ j, (source.stoich i j : ℝ) * u j = 0) :
    u 3 = u 0 ∧ u 1 = 3 * u 0 / 2 ∧ u 2 = u 0 ∧ u 4 = u 0 := by
  have h0 := hu ⟨0, by decide⟩
  have h1 := hu ⟨1, by decide⟩
  have h2 := hu ⟨2, by decide⟩
  have h3 := hu ⟨3, by decide⟩
  norm_num [source, SourceNetwork.stoich, Fin.sum_univ_succ] at h0 h1 h2 h3
  change -u 0 + u 3 = 0 at h0
  change -(4 * u 1) + 6 * u 3 = 0 at h1
  change 4 * u 0 + (-(2 * u 1) + (-(4 * u 2) + (u 3 + 2 * u 4))) = 0 at h2
  change -(2 * u 0) + (2 * u 2 + (-(2 * u 3) + 2 * u 4)) = 0 at h3
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem kernel_eq_multiple (u : Fin 5 → ℝ)
    (hu : ∀ i, ∑ j, (source.stoich i j : ℝ) * u j = 0) :
    ∀ j, u j = (u 0 / 2) * flux j := by
  obtain ⟨h3, h1, h2, h4⟩ := kernel_coordinates u hu
  intro j
  fin_cases j
  · change u 0 = (u 0 / 2) * 2
    ring
  · change u 1 = (u 0 / 2) * 3
    linarith
  · change u 2 = (u 0 / 2) * 2
    linarith
  · change u 3 = (u 0 / 2) * 2
    linarith
  · change u 4 = (u 0 / 2) * 2
    linarith

/-- A deleted channel forces every balanced flux to vanish. This conclusion
does not presume an equilibrium: it also applies to integrated orbit fluxes. -/
theorem kernel_zero_of_missing_channel (u : Fin 5 → ℝ)
    (hu : ∀ i, ∑ j, (source.stoich i j : ℝ) * u j = 0)
    (j : Fin 5) (hj : u j = 0) : u = 0 := by
  have hc := kernel_eq_multiple u hu
  have hz : u 0 / 2 = 0 := by
    have hm : (u 0 / 2) * flux j = 0 := (hc j).symm.trans hj
    exact (mul_eq_zero.mp hm).resolve_right (ne_of_gt (flux_pos j))
  funext k
  simpa [hz] using hc k

end OscillatoryCores
