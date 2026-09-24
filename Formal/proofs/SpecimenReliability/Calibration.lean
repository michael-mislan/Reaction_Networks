import proofs.SpecimenReliability.PreparationLoss

namespace SpecimenReliability
noncomputable section
open scoped BigOperators

/-- Recorded paired binary reference outcomes: neither, first only, second only, both.
The product law is conditional on the complete recovery state, not unconditional. -/
def referencePath (x y : ℝ) : Fin 4 → ℝ :=
  ![(1-x)*(1-y),x*(1-y),(1-x)*y,x*y]

theorem reference_as_corners (x y : ℝ) : referencePath x y = corners x y (x*y) := by
  funext i
  fin_cases i <;> simp [referencePath, corners] <;> ring

def referenceLaw {S : Type*} [Fintype S] (μ x y : S → ℝ) (j : Fin 4) : ℝ :=
  ∑ s, μ s * referencePath (x s) (y s) j

theorem reference_law {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hs : ∑ s, μ s = 1) :
    referenceLaw μ x y = corners (mean μ x) (mean μ y) (mean μ (fun s => x s*y s)) := by
  funext j
  simp only [referenceLaw, reference_as_corners]
  fin_cases j <;>
    simp [corners, mean, mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hs]

def discordant : Fin 4 → Bool := ![false,true,true,false]

def calibrationPass (p r q : ℝ) (m : ℕ) : ℝ :=
  ∑ h : Fin m → Fin 4, ∏ i,
    if discordant (h i) then corners p r q (h i) else 0

theorem calibration_pass (p r q : ℝ) (m : ℕ) :
    calibrationPass p r q m = (p+r-2*q)^m := by
  unfold calibrationPass
  rw [← Fintype.sum_pow (fun j => if discordant j then corners p r q j else 0) m]
  congr 1
  norm_num [discordant, corners, Fin.sum_univ_succ]
  ring

theorem moments_feasible {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hs : ∑ s, μ s = 1)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1) :
    0 ≤ mean μ (fun s => x s*y s) ∧
    mean μ (fun s => x s*y s) ≤ mean μ x ∧
    mean μ (fun s => x s*y s) ≤ mean μ y ∧
    mean μ x+mean μ y-1 ≤ mean μ (fun s => x s*y s) := by
  have hq : 0 ≤ mean μ (fun s => x s*y s) :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (mul_nonneg (hx s).1 (hy s).1))
  have hqp : mean μ (fun s => x s*y s) ≤ mean μ x := by
    apply Finset.sum_le_sum
    intro s _
    exact mul_le_mul_of_nonneg_left (by nlinarith [(hx s).1, (hy s).2] : x s*y s ≤ x s) (hμ s)
  have hqr : mean μ (fun s => x s*y s) ≤ mean μ y := by
    apply Finset.sum_le_sum
    intro s _
    exact mul_le_mul_of_nonneg_left (by nlinarith [(hy s).1, (hx s).2] : x s*y s ≤ y s) (hμ s)
  have hl := Finset.sum_nonneg (s := Finset.univ) (fun s _ =>
    mul_nonneg (hμ s) (mul_nonneg (sub_nonneg.mpr (hx s).2) (sub_nonneg.mpr (hy s).2)))
  have he : (∑ s, μ s*((1-x s)*(1-y s))) =
      1-mean μ x-mean μ y+mean μ (fun s => x s*y s) := by
    have he' (s : S) : μ s*((1-x s)*(1-y s)) =
        μ s-μ s*x s-μ s*y s+μ s*(x s*y s) := by ring
    simp only [he', Finset.sum_add_distrib, Finset.sum_sub_distrib, hs, mean]
  rw [he] at hl
  exact ⟨hq,hqp,hqr,by linarith⟩

/-- Three independent discordances control the entire future reporting event.
This elementary polynomial replaces an assumed confidence interval. -/
theorem cubic_gate_bound (r H : ℝ) (hr : 0 ≤ r ∧ r ≤ 1)
    (hH : 1/4 ≤ H ∧ H ≤ 1) : r^3 * (1-r*(1-H)) ≤ H := by
  have hr0 : 0 ≤ r := hr.1
  have hs : 0 ≤ (1-r)^2*(3*r^2+2*r+1) := by positivity
  have hr4 : r^4 ≤ 1 := pow_le_one₀ hr.1 hr.2
  have hm : 0 ≤ (H-1/4)*(1-r^4) := mul_nonneg (by linarith) (by linarith)
  nlinarith only [hs,hm]

theorem discordance_interval (p r q : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p)
    (hqr : q ≤ r) (hl : p+r-1 ≤ q) :
    0 ≤ p+r-2*q ∧ p+r-2*q ≤ 1 := by constructor <;> linarith

end
end SpecimenReliability
