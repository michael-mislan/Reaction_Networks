import proofs.CompositionalMemory.GenericUnitReactionMoments
import proofs.CompositionalMemory.ExchangeMoments

namespace CompositionalMemory

/-- Incoming and outgoing exchange are separate channels. Uniformity uses
the total row weight, with no bound on the number of neighbors. -/
theorem explicit_exchange_energy_moments {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y b : V) (w z : ι → ℝ) (zi Z κ v L r : ℝ)
    (hv : 0 < v) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, 0 ≤ z j ∧ z j ≤ Z)
    (hzi : 0 ≤ zi ∧ zi ≤ Z) (hrow : ∑ j, w j ≤ κ)
    (hop : ∀ x q, |Q x q| ≤ L*‖x‖*‖q‖)
    (hy : ‖y‖ ≤ r) (hb : ‖b‖ ≤ 1) :
    let ν : ι ⊕ ι → V := Sum.elim (fun _ => -b) (fun _ => b)
    let a : ι ⊕ ι → ℝ := Sum.elim (fun j => w j*zi) (fun j => w j*z j)
    (∑ j, v*a j*(Q (y+(1/v) • ν j) (y+(1/v) • ν j)-Q y y)) ≤
      4*L*r*Z*κ+2*L*Z*κ/v ∧
    (∑ j, v*a j*(Q (y+(1/v) • ν j) (y+(1/v) • ν j)-Q y y)^2) ≤
      16*L^2*r^2*Z*κ/v+4*L^2*Z*κ/v^3 := by
  let ν : ι ⊕ ι → V := Sum.elim (fun _ => -b) (fun _ => b)
  let a : ι ⊕ ι → ℝ := Sum.elim (fun j => w j*zi) (fun j => w j*z j)
  have ha (j) : 0 ≤ a j := by
    cases j with
    | inl j => exact mul_nonneg (hw j) hzi.1
    | inr j => exact mul_nonneg (hw j) (hz j).1
  have hA : ∑ j, a j ≤ 2*Z*κ := by
    rw [Fintype.sum_sum_type]
    change (∑ j, w j*zi)+(∑ j, w j*z j) ≤ _
    rw [← Finset.sum_add_distrib]
    simpa only [mul_add] using
      exchange_activity_bound w z zi Z κ hw (fun j => (hz j).2) hzi.2 hZ hrow
  have hν (j) : ‖ν j‖ ≤ 1 := by
    cases j with
    | inl j => simpa only [ν,Sum.elim_inl,norm_neg] using hb
    | inr j => exact hb
  have h := unit_reaction_energy_moments Q hQ y ν a v (2*Z*κ) L r
    hv hL hr ha hA hop hy hν
  constructor
  · convert h.1 using 1
    ring
  · convert h.2 using 1
    ring

end CompositionalMemory
