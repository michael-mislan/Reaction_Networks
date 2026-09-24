import proofs.CompositionalMemory.GenericFactorialSlots
import proofs.CompositionalMemory.GenericDensityDrift

namespace CompositionalMemory

theorem count_reaction_density_le {d : ℕ} (c v U : ℝ) (consume n : Fin d → ℕ)
    (hc : 0 ≤ c) (hv : 0 < v) (hu : ∀ j, (n j:ℝ)/v ≤ U) :
    countReactionDensity c v consume n ≤ c*U^(∑ j, consume j) := by
  rw [count_reaction_density_slots]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    _ ≤ ∏ j, U^(consume j) := by
      apply Finset.prod_le_prod
      · intro j _
        exact Finset.prod_nonneg (fun _ _ => by positivity)
      · intro j _
        calc
          _ ≤ ∏ _l : Fin (consume j), U := Finset.prod_le_prod
            (fun _ _ => by positivity)
            (fun l _ => ((clipped_density_factor (n j) l.val v hv).2.1).trans (hu j))
          _ = _ := by simp
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem mass_action_dissipation_at_birth_scale {V ι : Type*} {d : ℕ}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (y : V) (ν : ι → V)
    (consume : ι → Fin d → ℕ) (n : Fin d → ℕ) (c : ι → ℝ)
    (N v U L r lam D : ℝ) (hN : 0 < N) (hNv : N ≤ v)
    (hU : 0 ≤ U) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hc : ∀ j, 0 ≤ c j) (hu : ∀ a, (n a:ℝ)/v ≤ U)
    (hop : ∀ x z, |Q x z| ≤ L*‖x‖*‖z‖) (hy : ‖y‖ ≤ r)
    (hD : (∑ j, (c j*(∑ a, consume j a:ℕ)^2*(U+1)^(∑ a, consume j a))*‖ν j‖) ≤ D)
    (hd : 2*Q y (∑ j, (c j*(∏ a, ((n a:ℝ)/v)^(consume j a))) • ν j) ≤ -lam*r^2) :
    2*Q y (∑ j, countReactionDensity (c j) v (consume j) n • ν j) ≤
      -lam*r^2+(2*L*D/N)*r := by
  have hv : 0 < v := hN.trans_le hNv
  let actual := fun j => countReactionDensity (c j) v (consume j) n
  let ideal := fun j => c j*(∏ a, ((n a:ℝ)/v)^(consume j a))
  let error := fun j => c j*(∑ a, consume j a:ℕ)^2*(U+1)^(∑ a, consume j a)
  have hb (j) : |actual j-ideal j| ≤ error j/v :=
    count_reaction_density_bias (c j) v U (consume j) n (hc j) hv hU hu
  have herror : 0 ≤ ∑ j, error j*‖ν j‖ := Finset.sum_nonneg (fun j _ => by
    have hcj := hc j
    dsimp [error]
    positivity)
  have hD0 : 0 ≤ D := herror.trans hD
  have hbN : ‖(∑ j, actual j • ν j)-(∑ j, ideal j • ν j)‖ ≤ D/N :=
    ((density_drift_bias actual ideal error ν v hb).trans
      (div_le_div_of_nonneg_right hD hv.le)).trans (div_le_div_of_nonneg_left hD0 hN hNv)
  exact dissipation_with_density_bias Q y _ _ L r D N lam hL hr hop hy hbN hd

end CompositionalMemory
