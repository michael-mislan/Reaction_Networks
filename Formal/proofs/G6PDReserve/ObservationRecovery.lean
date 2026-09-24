import proofs.G6PDReserve.RecoveryClassification
import proofs.G6PDReserve.SourceRecovery
import proofs.G6PDReserve.SourceExistence

namespace G6PDReserve
noncomputable section
open Set

theorem closedRate_scalar (K g : ℝ) (_hK : 0 < K) :
    closedRate K g = scalarRate 2 (3/K) 3 56 g := by
  rw [closedRate, source_rate_polynomial _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
  unfold scalarRate
  have he : (3:ℝ)*7+(56-g)*7+(56-g)*7+3*7*(g/K+0/125+0/520) =
      7*(2*(56-g)+(3/K)*g+3) := by ring
  norm_num only [one_mul] at he ⊢
  rw [he]
  rw [show (56-g)*7 = 7*(56-g) by ring]
  exact mul_div_mul_left _ _ (by norm_num : (7:ℝ) ≠ 0)

theorem target_rate_formula (K : ℝ) (hK : 0 < K) :
    closedRate K 28 = 28*K/(59*K+84) := by
  rw [closedRate_scalar K 28 hK]
  unfold scalarRate
  field_simp
  ring

theorem exact_recovery_boundary (K : ℝ) (hK : 0 < K) :
    3/10 < closedRate K 28 ↔ 252/103 < K := by
  rw [target_rate_formula K hK, lt_div_iff₀ (show 0 < 59*K+84 by positivity)]
  constructor <;> intro h <;> linarith

def functionalAssay (K : ℝ) : ℝ := K/(3*K+56)

theorem one_assay_decides_margin (K : ℝ) (hK : 0 < K) :
    3/10 < closedRate K 28 ↔ 9/233 < functionalAssay K := by
  rw [exact_recovery_boundary K hK, functionalAssay,
    lt_div_iff₀ (show 0 < 3*K+56 by positivity)]
  constructor <;> intro h <;> linarith

theorem assay_band_target_bound (K : ℝ) (hK : 0 < K)
    (hy : 6/25 ≤ functionalAssay K) : 112/243 ≤ closedRate K 28 := by
  have hden : 0 < 3*K+56 := by positivity
  have hKK : 48 ≤ K := by
    have := (le_div_iff₀ hden).mp hy
    linarith
  rw [target_rate_formula K hK]
  apply (le_div_iff₀ (show 0 < 59*K+84 by positivity)).mpr
  linarith

/-- One designed noisy observation supplies a uniform deadline for every
pool-valued differentiable solution. Existence is a separate named obligation. -/
theorem observation_implies_recovery (K : ℝ) (hK : 0 < K)
    (hy : 6/25 ≤ functionalAssay K) (g : ℝ → ℝ) (h0 : g 0 = 10)
    (hpool : ∀ t ∈ Icc 0 (43740/391), g t ∈ Icc 0 56)
    (hd : ∀ t ∈ Icc 0 (43740/391), HasDerivAt g (closedRate K (g t)-3/10) t) :
    ∃ t ∈ Icc (0:ℝ) (43740/391), 28 ≤ g t := by
  have htime : (28-g 0)/(391/2430) = (43740/391:ℝ) := by rw [h0]; norm_num
  have hh := positive_drift_reaches g 28 (391/2430) (by norm_num) (by rw [h0]; norm_num)
    (by
      rw [htime]
      intro t ht
      simpa only [(hd t ht).deriv] using hd t ht)
    (by
      rw [htime]
      intro t ht hbelow
      rw [(hd t ht).deriv]
      have hanti : AntitoneOn (closedRate K) (Icc 0 56) := by
        change AntitoneOn (fun x => closedRate K x) (Icc 0 56)
        simp_rw [closedRate_scalar K _ hK]
        exact (scalar_rate_strictAnti 2 (3/K) 3 56 (by norm_num) (by positivity)
          (by norm_num) (by norm_num)).antitoneOn
      have hr := hanti (hpool t ht) (show (28:ℝ) ∈ Icc 0 56 by constructor <;> norm_num) hbelow.le
      have hb := assay_band_target_bound K hK hy
      linarith)
  rwa [htime] at hh

theorem observation_band_nonempty :
    0 < (56:ℝ) ∧ 6/25 ≤ functionalAssay 56 ∧ functionalAssay 56 ≤ 13/50 := by
  norm_num [functionalAssay]

/-- The exact K boundary classifies actual solutions, including the equality
case. No supplied ODE trajectory is an input hypothesis. -/
theorem exact_boundary_with_existence (K : ℝ) (hK : 0 < K) :
    (∃ T > (0:ℝ), ∃ g : ℝ → ℝ, g 0 = 10 ∧
      (∀ t ∈ Icc 0 T, g t ∈ Icc 0 56) ∧
      (∀ t ∈ Icc 0 T, HasDerivAt g (closedRate K (g t)-3/10) t) ∧ 28 ≤ g T) ↔
      252/103 < K := by
  have hc := scalar_recovery_iff 2 (3/K) 3 56 (3/10) 10 28
    (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRate])
  simp_rw [← closedRate_scalar K _ hK] at hc
  exact hc.trans (exact_recovery_boundary K hK)

/-- Observation-to-function root for a nonempty designed assay class. Both the
trajectory and its recovery are proved to exist; no donor interpretation. -/
theorem observation_recovery_exists (K : ℝ) (hK : 0 < K)
    (hy : 6/25 ≤ functionalAssay K) :
    ∃ g : ℝ → ℝ, g 0 = 10 ∧
      (∀ t ∈ Icc 0 (43740/391), g t ∈ Icc 0 56) ∧
      (∀ t ∈ Icc 0 (43740/391), HasDerivAt g (closedRate K (g t)-3/10) t) ∧
      ∃ t ∈ Icc (0:ℝ) (43740/391), 28 ≤ g t := by
  obtain ⟨g,h0,hpool,hd⟩ := scalar_solution_exists 2 (3/K) 3 56 (3/10) 10 (43740/391)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num)
    (by constructor <;> norm_num) (by norm_num) (by norm_num [scalarRate])
  have hd' : ∀ t ∈ Icc 0 (43740/391), HasDerivAt g (closedRate K (g t)-3/10) t := by
    simpa only [closedRate_scalar K _ hK] using hd
  exact ⟨g,h0,hpool,hd',observation_implies_recovery K hK hy g h0 hpool hd'⟩

theorem observed_K56_recovery_exists :
    ∃ g : ℝ → ℝ, g 0 = 10 ∧
      (∀ t ∈ Icc 0 (43740/391), g t ∈ Icc 0 56) ∧
      (∀ t ∈ Icc 0 (43740/391), HasDerivAt g (closedRate 56 (g t)-3/10) t) ∧
      ∃ t ∈ Icc (0:ℝ) (43740/391), 28 ≤ g t :=
  observation_recovery_exists 56 observation_band_nonempty.1 observation_band_nonempty.2.1

end
end G6PDReserve
