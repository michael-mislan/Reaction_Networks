import proofs.CompositionalMemory.GenericMembraneGeometry

namespace CompositionalMemory

/-- Explicit shared-volume jumps, with the jump bounds discharged from one
uniform bilinear operator bound and concentration/consumption norm bounds. -/
theorem explicit_membrane_energy_moments {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ} (hk : 1 ≤ k) (i : Fin k)
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y u b : V) (z : Fin k → ℝ) (γ m N U Z L r : ℝ)
    (hγ : 0 ≤ γ) (hN : 0 < N) (hm : (k : ℝ)*N ≤ m)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hz0 : ∀ j, 0 ≤ z j) (hz : ∀ j, z j ≤ Z)
    (hop : ∀ v w, |Q v w| ≤ L*‖v‖*‖w‖)
    (hy : ‖y‖ ≤ r) (hu : ‖u‖ ≤ U) (hb : ‖b‖ ≤ 1) :
    let jump := fun j : Fin k => membraneVectorJump u b (if j=i then (k:ℝ) else 0) m
    (∑ j, (γ*(m/k)*z j)*(Q (y+jump j) (y+jump j)-Q y y)) ≤
      2*L*r*(γ*Z*(U+1))+L*(γ*Z*(U+1)^2/N) ∧
    (∑ j, (γ*(m/k)*z j)*(Q (y+jump j) (y+jump j)-Q y y)^2) ≤
      8*L^2*r^2*γ*Z*(U+1)^2/N+2*L^2*γ*Z*(U+1)^4/N^3 := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hm0 : 0 < m := lt_of_lt_of_le (mul_pos hk0 hN) hm
  have hbnd (j : Fin k) := membrane_vector_bilinear_bounds Q y u b L r U
    (if j=i then (k:ℝ) else 0) m hL hr hU
    (by split_ifs <;> positivity) (by linarith) hop hy hu hb
  exact generic_membrane_energy_moments hk i Q hQ y _ z γ m N U Z L r
    hγ hN hm hU hZ hL hr hz0 hz (fun j => (hbnd j).1) (fun j => (hbnd j).2)

end CompositionalMemory
