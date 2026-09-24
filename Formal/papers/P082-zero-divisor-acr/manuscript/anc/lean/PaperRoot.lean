import proofs.ACRZeroDivisors.CampaignRoot
import proofs.ACRZeroDivisors.ResidualBounds
import proofs.ACRZeroDivisors.ReactorAlgebra
import proofs.ACRZeroDivisors.ReactorStability
import proofs.ACRZeroDivisors.EnvZCertificates
import proofs.ACRZeroDivisors.ReleaseCosts
import proofs.ACRZeroDivisors.AssociatedTorsion
import proofs.ACRZeroDivisors.GeometryFixtures

namespace ACRZeroDivisors

/-- Preserves the independent original roots and combines the principal
extension interfaces. Geometry and nonlinear stability are conventional
manuscript proofs, not axioms or implicit premises of this certificate. -/
theorem paper_root : CampaignCertificate ∧
    (∀ (e h h0 B : ℝ), 0 < h0 → h0 ≤ |h| → |e*h| ≤ B → |e| ≤ B/h0) ∧
    (∀ (D ell delta p q k3 z : ℝ),
      Matrix.det !![z+D+ell+p+q,D+k3,D-delta;-p,z,0;-q,-k3,z+delta] =
      z^3+(D+ell+delta+p+q)*z^2+
      (delta*(D+ell)+p*(delta+k3+D)+D*q)*z+D*p*(delta+k3)) ∧
    (∀ (k : Fin 9 → ℝ) (x : Fin 7 → ℝ),
      k 8*envZField k x 6-(k 7+k 8)*(envZField k x 2-envZField k x 3) =
        x 1*(k 6*k 8*x 4-k 2*(k 7+k 8)) ∧
      k 2*envZField k x 6-k 6*x 4*(envZField k x 2-envZField k x 3) =
        x 6*(k 6*k 8*x 4-k 2*(k 7+k 8))) ∧
    (∀ (a : ℕ → ℝ) (n : ℕ), (∀ j, 0 ≤ a j) → (∀ j, a j ≤ 1) →
      1-(∏ j ∈ Finset.range n, a j) ≤ ∑ j ∈ Finset.range n, (1-a j)) :=
  ⟨campaign_root, residual_bound, reactor_characteristic, envZ_identities, product_loss_bound⟩

end ACRZeroDivisors
