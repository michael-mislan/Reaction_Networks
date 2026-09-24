import proofs.DisguisedToricAssemblies.CACNecessary
import proofs.DisguisedToricAssemblies.CACSufficient

namespace DisguisedToricAssemblies
open CoreCouplingCAC

/-- Arbitrarily many additional ordinary reaction complexes, with the eight
literal source complexes adjoined. Rows outside polynomial support are zero. -/
noncomputable def extendedComplexes {n : ℕ} (z : Fin n → Fin 4 → ℕ) :
    Fin 8 ⊕ Fin n → Fin 4 → ℝ := Sum.elim complexes (fun i k => (z i k : ℝ))

noncomputable def extendedRows {n : ℕ} (p : Rates) (x : State) :
    Fin 8 ⊕ Fin n → Fin 4 → ℝ :=
  Sum.elim (fun i k => activity x i*coefficient p i k) (fun _ _ => 0)

def ExtendedCertificate {n : ℕ} (p : Rates) (x : State)
    (z : Fin n → Fin 4 → ℕ) (q : (Fin 8 ⊕ Fin n) → (Fin 8 ⊕ Fin n) → ℝ) : Prop :=
  (∀ i j, 0 ≤ q i j) ∧ (∀ i, q i i = 0) ∧
  (∀ i, ∑ j, q i j = ∑ j, q j i) ∧
  (∀ i k, ∑ j, q i j*(extendedComplexes z j k-extendedComplexes z i k) =
    extendedRows p x i k)

theorem extended_dual_bound {n : ℕ} (p : Rates) (x : State)
    (z : Fin n → Fin 4 → ℕ) (q : (Fin 8 ⊕ Fin n) → (Fin 8 ⊕ Fin n) → ℝ)
    (hc : ExtendedCertificate p x z q) (h : Fin 8 → Fin 4 → ℝ) (P : Fin 8 → ℝ)
    (hs : ∀ i j, 0 ≤ (∑ k, h i k*(complexes j k-complexes i k))+P j-P i) :
    0 ≤ ∑ i, ∑ k, h i k*(activity x i*coefficient p i k) := by
  obtain ⟨H,Q,hHQ,hslack⟩ := complete_supports complexes h P (fun i k => (z i k : ℝ)) hs
  have hn := supporting_dual_nonneg q (extendedComplexes z) H (extendedRows p x) Q
    hc.1 hc.2.2.1 hc.2.2.2 hslack
  have hh : ∀ i, H (.inl i) = h i := fun i => (hHQ i).1
  simpa [Fintype.sum_sum_type, extendedRows, hh] using hn

theorem extended_stationary {n : ℕ} (p : Rates) (x : State)
    (z : Fin n → Fin 4 → ℕ) (q : (Fin 8 ⊕ Fin n) → (Fin 8 ⊕ Fin n) → ℝ)
    (hc : ExtendedCertificate p x z q) : Stationary p x := by
  have hd : ∀ k, sourceDerivative p x k = 0 := by
    intro k
    have hz := circulation_potential q (fun i => extendedComplexes z i k) hc.2.2.1
    simp_rw [hc.2.2.2] at hz
    have hh : (∑ i, activity x i*coefficient p i k) = 0 := by
      simpa [Fintype.sum_sum_type, extendedRows] using hz
    rwa [coefficient_source] at hh
  refine ⟨?_,?_,?_,?_⟩
  · have h := hd 0; rw [literal_source_adapter] at h; exact h
  · have h := hd 1; rw [literal_source_adapter] at h; exact h
  · have h := hd 2; rw [literal_source_adapter] at h; exact h
  · have h := hd 3; rw [literal_source_adapter] at h; exact h

theorem extended_necessary {n : ℕ} (p : Rates) (x : State)
    (z : Fin n → Fin 4 → ℕ) (q : (Fin 8 ⊕ Fin n) → (Fin 8 ⊕ Fin n) → ℝ)
    (hc : ExtendedCertificate p x z q) :
    Stationary p x ∧ 0 ≤ x.A-x.B*x.z ∧ p.e*(x.B-x.A^2) ≤ x.B := by
  have hs := extended_stationary p x z q hc
  have hK := extended_dual_bound p x z q hc currentH currentP current_support
  have hJ := extended_dual_bound p x z q hc dualH dualP dual_support
  rw [current_evaluation] at hK
  rw [dual_evaluation p x hs] at hJ
  exact ⟨hs,hK,by linarith⟩

/-- Coefficientwise complex-balanced realizability, allowing any finite number
of extra ordinary complexes. Fluxes are at the specified positive state. -/
def RealizableAt (p : Rates) (x : State) : Prop :=
  ∃ n, ∃ z : Fin n → Fin 4 → ℕ,
    ∃ q : (Fin 8 ⊕ Fin n) → (Fin 8 ⊕ Fin n) → ℝ, ExtendedCertificate p x z q

def DisguisedToric (p : Rates) : Prop := ∃ x : State, x.Positive ∧ RealizableAt p x

theorem finite_certificate_realizable (p : Rates) (x : State)
    (q : Fin 8 → Fin 8 → ℝ) (hc : FluxCertificate p x q) : RealizableAt p x := by
  let c : Fin 8 ⊕ Fin 0 → Fin 8 := Sum.elim id Fin.elim0
  refine ⟨0, Fin.elim0, (fun u v => q (c u) (c v)), ?_⟩
  refine ⟨fun u v => hc.1 _ _, fun u => hc.2.1 _, ?_, ?_⟩
  · intro u
    cases u with
    | inl i => simpa [c, Fintype.sum_sum_type] using hc.2.2.1 i
    | inr i => exact Fin.elim0 i
  · intro u k
    cases u with
    | inl i =>
      simpa [c, Fintype.sum_sum_type, extendedComplexes, extendedRows] using hc.2.2.2 i k
    | inr i => exact Fin.elim0 i

theorem cac_state_characterization (p : Rates) (x : State)
    (hp : p.Positive) (hx : x.Positive) :
    RealizableAt p x ↔ Stationary p x ∧ 0 ≤ x.A-x.B*x.z ∧ p.e*(x.B-x.A^2) ≤ x.B := by
  constructor
  · rintro ⟨n,z,q,hc⟩
    exact extended_necessary p x z q hc
  · rintro ⟨hs,hK,hJ⟩
    exact finite_certificate_realizable p x (flux p x) (cac_flux_certificate p x hp hx hs hK hJ)

end DisguisedToricAssemblies
