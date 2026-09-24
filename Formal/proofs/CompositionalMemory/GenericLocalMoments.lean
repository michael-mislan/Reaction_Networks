import proofs.CompositionalMemory.GenericDissipativeMoments
import proofs.CompositionalMemory.GenericMembraneBinding
import proofs.CompositionalMemory.GenericExchangeBinding

namespace CompositionalMemory

noncomputable def localChannelRate {ι : Type*} {k : ℕ}
    (a : ι → ℝ) (γ v : ℝ) (z w : Fin k → ℝ) (i : Fin k) :
    ι ⊕ (Fin k ⊕ (Fin k ⊕ Fin k)) → ℝ :=
  Sum.elim (fun j => v*a j) (Sum.elim (fun j => γ*v*z j)
    (Sum.elim (fun j => v*(w j*z i)) (fun j => v*(w j*z j))))

noncomputable def localChannelJump {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    {k : ℕ} (ν : ι → V) (u b : V) (v : ℝ) (i : Fin k) :
    ι ⊕ (Fin k ⊕ (Fin k ⊕ Fin k)) → V :=
  Sum.elim (fun j => (1/v) • ν j)
    (Sum.elim (fun j => membraneVectorJump u b (if j=i then (k:ℝ) else 0) (k*v))
      (Sum.elim (fun _ => (1/v) • (-b)) (fun _ => (1/v) • b)))

/-- Combined moments of the literal resident, shared-growth and paired
exchange channels. Every coefficient is independent of module count. -/
theorem generic_local_energy_moments {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {k : ℕ} (hk : 1 ≤ k) (i : Fin k)
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y u b : V) (ν : ι → V) (a : ι → ℝ) (z w : Fin k → ℝ)
    (v γ κ lam r A P R F U Z L : ℝ)
    (hv : 0 < v) (hγ : 0 ≤ γ) (hR : 0 ≤ R)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (ha : ∀ j, 0 ≤ a j) (hA : ∑ j, a j ≤ A)
    (hcross : ∀ j, |Q y (ν j)| ≤ P*r) (hquad : ∀ j, |Q (ν j) (ν j)| ≤ R)
    (hd : 2*Q y (∑ j, a j • ν j) ≤ -lam*r^2+F*r)
    (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, 0 ≤ z j ∧ z j ≤ Z)
    (hrow : ∑ j, w j ≤ κ)
    (hop : ∀ x q, |Q x q| ≤ L*‖x‖*‖q‖)
    (hy : ‖y‖ ≤ r) (hu : ‖u‖ ≤ U) (hb : ‖b‖ ≤ 1) :
    let rate := localChannelRate a γ v z w i
    let jump := localChannelJump ν u b v i
    (∑ j, rate j*(Q (y+jump j) (y+jump j)-Q y y)) ≤
      -lam*r^2+(F+2*L*γ*Z*(U+1)+4*L*Z*κ)*r+
        (A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)/v ∧
    (∑ j, rate j*(Q (y+jump j) (y+jump j)-Q y y)^2) ≤
      (8*A*P^2+8*L^2*γ*Z*(U+1)^2+16*L^2*Z*κ)*r^2/v+
        (2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/v^3 := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hvol : ((k:ℝ)*v)/k=v := by field_simp
  have hres := dissipative_reaction_energy_moments Q hQ y ν a v lam r A P R F
    hv hR ha hA hcross hquad hd
  have hmem := explicit_membrane_energy_moments hk i Q hQ y u b z γ (k*v) v U Z L r
    hγ hv le_rfl hU hZ hL hr (fun j => (hz j).1) (fun j => (hz j).2) hop hy hu hb
  simp only [hvol] at hmem
  have hex := explicit_exchange_energy_moments Q hQ y b w z (z i) Z κ v L r
    hv hZ hL hr hw hz (hz i) hrow hop hy hb
  dsimp only at hex hmem
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] at hex
  simp only [localChannelRate,localChannelJump,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  constructor
  · have h := add_le_add hres.1 (add_le_add hmem.1 hex.1)
    convert h using 1
    ring
  · have h := add_le_add hres.2 (add_le_add hmem.2 hex.2)
    convert h using 1
    ring

end CompositionalMemory
