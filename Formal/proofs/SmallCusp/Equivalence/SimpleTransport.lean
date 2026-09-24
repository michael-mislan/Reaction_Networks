import proofs.SmallCusp.Source.SourceClasses

/-!
# Transport of cusp certificates under simple equivalence

Independent positive column scalings are absorbed into the corresponding rate
coordinates.  This file proves the resulting literal identities for the field,
its first two state derivatives, and its two rate-unfolding rows.
-/

namespace SmallCusp

noncomputable def simpleRateTransport {m : ℕ} (e : Equiv.Perm (Fin m))
    (c k : Fin m → ℝ) : Fin m → ℝ :=
  fun s => k (e.symm s) / c (e.symm s)

theorem simpleRateTransport_positive {m : ℕ} (e : Equiv.Perm (Fin m))
    {c k : Fin m → ℝ} (hc : PositiveVector c) (hk : PositiveVector k) :
    PositiveVector (simpleRateTransport e c k) := by
  intro s
  exact div_pos (hk (e.symm s)) (hc (e.symm s))

section Identities

variable {m : ℕ} {Q P : SmallPlanarNetwork m}
variable (e : Equiv.Perm (Fin m)) (c : Fin m → ℝ)
variable (hc : PositiveVector c)
variable (hReact : ∀ r, P.reactant (e r) = Q.reactant r)
variable (hStoich : ∀ i r, (P.stoich i (e r) : ℝ) = c r * (Q.stoich i r : ℝ))

include hReact in
theorem simple_monomial_transport (r : Fin m) (x : Species → ℝ) :
    P.monomial (e r) x = Q.monomial r x := by
  unfold SmallPlanarNetwork.monomial
  rw [hReact r]

include hReact in
theorem simple_multiDerivative_transport (r : Fin m) (d : Species → ℕ)
    (x : Species → ℝ) :
    P.multiDerivativeMonomial (e r) d x = Q.multiDerivativeMonomial r d x := by
  unfold SmallPlanarNetwork.multiDerivativeMonomial
  rw [hReact r]

private theorem simple_sum_reindex {A : Type} [AddCommMonoid A]
    (f : Fin m → A) :
    (∑ s, f s) = ∑ r, f (e r) :=
  (Equiv.sum_comp e f).symm

include hc hReact hStoich

theorem simple_massAction_transport (k : Fin m → ℝ) (x : Species → ℝ)
    (i : Species) :
    P.massAction (simpleRateTransport e c k) x i = Q.massAction k x i := by
  unfold SmallPlanarNetwork.massAction
  rw [simple_sum_reindex e]
  apply Finset.sum_congr rfl
  intro r _
  rw [hStoich i r, simple_monomial_transport e hReact r x]
  simp only [simpleRateTransport, Equiv.symm_apply_apply]
  field_simp [ne_of_gt (hc r)]

theorem simple_jacobian_transport (k : Fin m → ℝ) (x : Species → ℝ)
    (i j : Species) :
    P.jacobian (simpleRateTransport e c k) x i j = Q.jacobian k x i j := by
  unfold SmallPlanarNetwork.jacobian
  rw [simple_sum_reindex e]
  apply Finset.sum_congr rfl
  intro r _
  rw [hStoich i r,
    simple_multiDerivative_transport e hReact r
      (SmallPlanarNetwork.unitMultiIndex j) x]
  simp only [simpleRateTransport, Equiv.symm_apply_apply]
  field_simp [ne_of_gt (hc r)]

theorem simple_hessian_transport (k : Fin m → ℝ) (x : Species → ℝ)
    (i j l : Species) :
    P.hessian (simpleRateTransport e c k) x i j l = Q.hessian k x i j l := by
  unfold SmallPlanarNetwork.hessian
  rw [simple_sum_reindex e]
  apply Finset.sum_congr rfl
  intro r _
  rw [hStoich i r,
    simple_multiDerivative_transport e hReact r
      (SmallPlanarNetwork.pairMultiIndex j l) x]
  simp only [simpleRateTransport, Equiv.symm_apply_apply]
  field_simp [ne_of_gt (hc r)]

theorem simple_jacobianApply_transport (k : Fin m → ℝ) (x v : Species → ℝ)
    (i : Species) :
    P.jacobianApply (simpleRateTransport e c k) x v i =
      Q.jacobianApply k x v i := by
  unfold SmallPlanarNetwork.jacobianApply
  apply Finset.sum_congr rfl
  intro j _
  rw [simple_jacobian_transport e c hc hReact hStoich]

theorem simple_hessianApply_transport (k : Fin m → ℝ)
    (x u v : Species → ℝ) (i : Species) :
    P.hessianApply (simpleRateTransport e c k) x u v i =
      Q.hessianApply k x u v i := by
  unfold SmallPlanarNetwork.hessianApply
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [simple_hessian_transport e c hc hReact hStoich]

theorem simple_rateFieldVariation_transport (u : Fin m → ℝ)
    (x : Species → ℝ) (i : Species) :
    P.rateFieldVariation (simpleRateTransport e c u) x i =
      Q.rateFieldVariation u x i := by
  unfold SmallPlanarNetwork.rateFieldVariation
  rw [simple_sum_reindex e]
  apply Finset.sum_congr rfl
  intro r _
  rw [hStoich i r, simple_monomial_transport e hReact r x]
  simp only [simpleRateTransport, Equiv.symm_apply_apply]
  field_simp [ne_of_gt (hc r)]

theorem simple_rateJacobianVariation_transport (u : Fin m → ℝ)
    (x q : Species → ℝ) (i : Species) :
    P.rateJacobianVariation (simpleRateTransport e c u) x q i =
      Q.rateJacobianVariation u x q i := by
  unfold SmallPlanarNetwork.rateJacobianVariation
  rw [simple_sum_reindex e]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  rw [hStoich i r,
    simple_multiDerivative_transport e hReact r
      (SmallPlanarNetwork.unitMultiIndex j) x]
  simp only [simpleRateTransport, Equiv.symm_apply_apply]
  field_simp [ne_of_gt (hc r)]

theorem simple_dot_rateFieldVariation_transport (p x : Species → ℝ)
    (u : Fin m → ℝ) :
    dot p (P.rateFieldVariation (simpleRateTransport e c u) x) =
      dot p (Q.rateFieldVariation u x) := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  rw [simple_rateFieldVariation_transport e c hc hReact hStoich]

theorem simple_dot_rateJacobianVariation_transport (p x q : Species → ℝ)
    (u : Fin m → ℝ) :
    dot p (P.rateJacobianVariation (simpleRateTransport e c u) x q) =
      dot p (Q.rateJacobianVariation u x q) := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  rw [simple_rateJacobianVariation_transport e c hc hReact hStoich]

end Identities

end SmallCusp
