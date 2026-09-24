import proofs.DisguisedToricAssemblies.CACFluxConstruction
import proofs.DisguisedToricAssemblies.BalancedFlux

namespace DisguisedToricAssemblies
open CoreCouplingCAC

theorem positive_part_difference (J : ℝ) : max J 0-max (-J) 0 = J := by
  by_cases h : 0 ≤ J
  · rw [max_eq_left h, max_eq_right (by linarith : -J ≤ 0)]
    ring
  · have hn : J ≤ 0 := le_of_not_ge h
    rw [max_eq_right hn, max_eq_left (by linarith : 0 ≤ -J)]
    ring

theorem cac_flux_certificate (p : Rates) (x : State)
    (hp : p.Positive) (hx : x.Positive) (hs : Stationary p x)
    (hK : 0 ≤ x.A-x.B*x.z) (hJ : p.e*(x.B-x.A^2) ≤ x.B) :
    FluxCertificate p x (flux p x) := by
  have hnn := flux_nonneg p x hp hx hs hK hJ
  have hj := positive_part_difference (p.e*(x.B-x.A^2))
  obtain ⟨ha,hb,hz,hh⟩ := hs
  dsimp [fA] at ha
  dsimp [fB] at hb
  dsimp [fZ] at hz
  dsimp [fH] at hh
  have hk : x.A-x.B*x.z = p.u*x.z+2*(p.v*x.z^2)-3*x.H := by linarith
  have hhh : p.u*x.z+p.v*x.z^2 = (2+p.d)*x.H := by linarith
  refine ⟨hnn, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [flux, fluxTable]
  · unfold flux
    apply flux_table_balanced
    · linear_combination ha + 2*hj
    · linear_combination hb - hj
    · linear_combination -hj
    · exact hk
  · intro i k
    unfold flux
    rw [flux_table_drift _ _ _ _ _ _ _ _ _ _ _ _ _ ((2+p.d)*x.H) hk hhh]
    fin_cases i <;> fin_cases k <;> norm_num [activity, coefficient] <;> ring

theorem activity_positive (x : State) (hx : x.Positive) : ∀ i, 0 < activity x i := by
  intro i
  fin_cases i <;> norm_num [activity]
  · exact hx.1
  · exact mul_pos hx.2.1 hx.2.2.1
  · exact hx.2.2.1
  · exact hx.2.2.2
  · exact sq_pos_of_pos hx.2.2.1
  · exact hx.2.1
  · exact sq_pos_of_pos hx.1

/-- Explicit rates on the eight original complexes. Positive entries are the edges. -/
noncomputable def realizingRates (p : Rates) (x : State) (i j : Fin 8) : ℝ :=
  flux p x i j / activity x i

theorem cac_constructive_sufficiency (p : Rates) (x : State)
    (hp : p.Positive) (hx : x.Positive) (hs : Stationary p x)
    (hK : 0 ≤ x.A-x.B*x.z) (hJ : p.e*(x.B-x.A^2) ≤ x.B) :
    (∀ i j, 0 ≤ realizingRates p x i j) ∧
    (∀ i j, 0 < realizingRates p x i j ↔ 0 < flux p x i j) ∧
    (∀ i, ∑ j, realizingRates p x i j * activity x i =
      ∑ j, realizingRates p x j i * activity x j) ∧
    (∀ i k, ∑ j, realizingRates p x i j * (complexes j k-complexes i k) =
      coefficient p i k) := by
  have hc := cac_flux_certificate p x hp hx hs hK hJ
  exact reconstruct_rates complexes (coefficient p) (activity x) (flux p x)
    (activity_positive x hx) hc.1 hc.2.2.1 hc.2.2.2

end DisguisedToricAssemblies
