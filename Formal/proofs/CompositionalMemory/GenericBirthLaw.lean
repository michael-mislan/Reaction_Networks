import proofs.CompositionalMemory.GenericBirthDomain
import proofs.CompositionalMemory.GenericPartitionReturn
import proofs.HeritableCompositions.FiniteLaw

namespace CompositionalMemory
open HeritableCompositions

theorem norm_coercive_coordinate {d : ℕ}
    (Q : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hcoerc : ∀ y, c*‖y‖^2 ≤ Q y y) (y : Fin d → ℝ) (a : Fin d) :
    c*(y a)^2 ≤ Q y y := by
  have hcoord : ‖y a‖ ≤ ‖y‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mp le_rfl a
  rw [Real.norm_eq_abs] at hcoord
  have hs := (sq_le_sq₀ (abs_nonneg (y a)) (norm_nonneg y)).mpr hcoord
  rw [sq_abs] at hs
  exact (mul_le_mul_of_nonneg_left hs hc).trans (hcoerc y)

noncomputable def generalDaughterLaw {k d : ℕ} (n : Fin k → Fin d → ℕ) :
    FiniteLaw {x : GeneralDraw k d // x ∈ generalDraws n} := {
  mass := fun x => generalDrawWeight n x.val
  nonneg := fun x => general_draw_weight_nonneg n x.val
  total := by rw [Finset.sum_coe_sort]; exact general_draw_weight_sum n }

/-- Push forward one fair allocation into complementary finite newborns.
Failure means a daughter lies outside the specified birth region. -/
noncomputable def generalPartitionLaw {k d : ℕ} (N C : ℕ) (hN : 0 < N)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (center : Fin k → Fin d → ℝ) (c radius birth : ℝ) (hc : 0 < c)
    (hr : 0 ≤ radius) (hb : birth ≤ c*radius^2)
    (hcenter : ∀ i a, center i a ≤ (C:ℝ)-radius)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y) (n : Fin k → Fin d → ℕ) :
    FiniteLaw (GeneralBirthOutcome N C center (fun i y => Q i y y) birth) := by
  classical
  have hE := fun i => norm_coercive_coordinate (Q i) c hc.le (hcoerc i)
  exact (generalDaughterLaw n).bind (fun x =>
    if h : generalBothReturn N Q center birth n x.val then
      FiniteLaw.pure (some
        (⟨(fun i a => x.val (i,a)),(mem_generalBirthCounts N C hN center (fun i y => Q i y y)
          c radius birth hc hr hb hcenter hE _).mpr (fun i => (h i).1)⟩,
         ⟨(fun i a => n i a-x.val (i,a)),(mem_generalBirthCounts N C hN center (fun i y => Q i y y)
          c radius birth hc hr hb hcenter hE _).mpr (fun i => (h i).2)⟩))
    else FiniteLaw.pure none)

theorem generalPartitionLaw_failure_eq {k d : ℕ} (N C : ℕ) (hN : 0 < N)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (center : Fin k → Fin d → ℝ) (c radius birth : ℝ) (hc : 0 < c)
    (hr : 0 ≤ radius) (hb : birth ≤ c*radius^2)
    (hcenter : ∀ i a, center i a ≤ (C:ℝ)-radius)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y) (n : Fin k → Fin d → ℕ) :
    (generalPartitionLaw N C hN Q center c radius birth hc hr hb hcenter hcoerc n).mass none =
      ∑ x ∈ generalDraws n, generalDrawWeight n x*
        (if ¬ generalBothReturn N Q center birth n x then 1 else 0) := by
  classical
  unfold generalPartitionLaw FiniteLaw.bind
  change (∑ x : {x : GeneralDraw k d // x ∈ generalDraws n}, generalDrawWeight n x.val*_) = _
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with h
  · simp [FiniteLaw.pure,h]
  · simp [FiniteLaw.pure,h]

end CompositionalMemory
