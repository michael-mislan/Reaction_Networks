import proofs.G6PDReserve.SourceRate
import proofs.G6PDReserve.DriftComparison

/-! A conditional closed NADP(H) module with literal G6PD kinetics. Fixed
substrates, pool closure and constant demand are declared model assumptions.
The result is not an erythrocyte protection or ATP-service theorem. -/
namespace G6PDReserve
noncomputable section
open Set

def closedRate (Kh g : ℝ) : ℝ := shimoRate 1 3 7 Kh 125 520 (56-g) 7 g 0 0

theorem strong_rate_formula (g : ℝ) :
    closedRate 1 g = 7*(56-g)/(805+7*g) := by
  rw [closedRate, source_rate_polynomial _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
  norm_num
  congr 1 <;> ring

theorem weak_rate_formula (g : ℝ) :
    closedRate 56 g = 7*(56-g)/(805-(109/8)*g) := by
  rw [closedRate, source_rate_polynomial _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
  norm_num
  congr 1 <;> ring

theorem strong_rate_upper (g : ℝ) (hg : 0 ≤ g) (hP : g ≤ 56) :
    closedRate 1 g ≤ (56-g)/115 := by
  rw [strong_rate_formula]
  have hden : 0 < 805+7*g := by linarith
  apply (div_le_iff₀ hden).mpr
  have hprod := mul_nonneg hg (sub_nonneg.mpr hP)
  nlinarith

theorem weak_positive_drift (g : ℝ) (hg : g ≤ 28) :
    197/1210 ≤ closedRate 56 g - 3/10 := by
  rw [weak_rate_formula]
  have hden : 0 < 805-(109/8)*g := by linarith
  have hr : (56:ℝ)/121 ≤ 7*(56-g)/(805-(109/8)*g) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  linarith

theorem strong_inhibition_no_return (g : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (h0 : g 0 = 10)
    (hpool : ∀ t ∈ Icc 0 T, 0 ≤ g t ∧ g t ≤ 56)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt g (closedRate 1 (g t)-3/10) t) :
    g T < 28 := by
  have hb := upper_drift_comparison g (fun t => closedRate 1 (g t)-3/10)
    (1/115) (43/2) T hT hd (by
      intro t ht
      have hu := strong_rate_upper (g t) (hpool t ht).1 (hpool t ht).2
      linarith)
  rw [h0] at hb
  have he := Real.exp_pos (-(1/115)*T)
  nlinarith

/-- Every differentiable solution with this initial condition reaches the
target by 21780/197 time units. This theorem is conditional on a solution;
existence and the physiological adapter are separate obligations. -/
theorem weak_inhibition_return (g : ℝ → ℝ) (h0 : g 0 = 10)
    (hd : ∀ t ∈ Icc 0 (21780/197), HasDerivAt g (closedRate 56 (g t)-3/10) t) :
    ∃ t ∈ Icc (0:ℝ) (21780/197), 28 ≤ g t := by
  by_contra hn
  have hbelow : ∀ t ∈ Icc (0:ℝ) (21780/197), g t < 28 := by
    intro t ht
    by_contra h
    exact hn ⟨t, ht, le_of_not_gt h⟩
  let F : ℝ → ℝ := fun t => g t - (197/1210)*t
  have hF (t : ℝ) (ht : t ∈ Icc (0:ℝ) (21780/197)) :
      HasDerivAt F (closedRate 56 (g t)-3/10-197/1210) t := by
    simpa [F] using (hd t ht).sub ((hasDerivAt_id t).const_mul (197/1210))
  have hm : MonotoneOn F (Icc (0:ℝ) (21780/197)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro t ht
      exact (hF t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hF t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hF t (interior_subset ht)).deriv]
      have h := weak_positive_drift (g t) (le_of_lt (hbelow t (interior_subset ht)))
      linarith
  have hstart : (0:ℝ) ∈ Icc (0:ℝ) (21780/197) := by constructor <;> norm_num
  have hend : (21780/197:ℝ) ∈ Icc (0:ℝ) (21780/197) := by constructor <;> norm_num
  have hb := hm hstart hend (by norm_num)
  dsimp [F] at hb
  rw [h0] at hb
  have hu := hbelow _ hend
  norm_num at hb
  linarith

end
end G6PDReserve
