import proofs.MultiConsumerPermanence.CompositionRecovery

namespace MultiConsumerPermanence
open scoped BigOperators
open Filter Topology

theorem weighted_growth_error {n : ℕ} (x a : Fin n → ℝ) (g eps : ℝ)
    (hx : ∀ j, 0 ≤ x j) (ha : ∀ j, |a j-g| ≤ eps) (i : Fin n) :
    (∑ j, x j*a j)-a i*total x ≤ 2*eps*total x := by
  have hb (j : Fin n) : x j*(a j-a i) ≤ x j*(2*eps) := by
    apply mul_le_mul_of_nonneg_left _ (hx j)
    have hj := abs_le.mp (ha j)
    have hi := abs_le.mp (ha i)
    linarith only [hj.2,hi.1]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hb j)
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul] at hs
  simpa only [mul_comm,total] using hs

theorem weighted_loss_lower {n : ℕ} (x rho : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hr : ∀ j, (n:ℝ)/2 ≤ rho j) :
    (total x)^2/2 ≤ ∑ j, rho j*(x j)^2 := by
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hr j) (sq_nonneg (x j)))
  rw [← Finset.mul_sum] at hh
  have hc := (squares_bounds x hx).2
  change (n:ℝ)/2*squares x ≤ _ at hh
  linarith only [hh,hc]

theorem heterogeneous_ratio_drift (S A H x a rho N eps s M : ℝ)
    (hx : 0 < x) (hs : 0 < s) (hS : s ≤ S) (hM : S ≤ M)
    (hN : 0 ≤ N) (hr : rho ≤ N) (heps : eps ≤ s/8)
    (hA : A-a*S ≤ 2*eps*S) (hH : S^2/2 ≤ H) :
    ((A-H)*x-S*(x*(a-rho*x)))/x^2 ≤ N*M-(s/4)*(S/x) := by
  have hid : ((A-H)*x-S*(x*(a-rho*x)))/x^2 =
      (A-a*S-H)/x+rho*S := by
    field_simp
    ring
  rw [hid]
  have hnum : A-a*S-H ≤ 2*eps*S-S^2/2 := by linarith only [hA,hH]
  have hdiv := div_le_div_of_nonneg_right hnum hx.le
  have hu : 0 ≤ S/x := div_nonneg (hs.le.trans hS) hx.le
  have hdamp := mul_le_mul_of_nonneg_right
    (show 2*eps-S/2 ≤ -(s/4) by linarith only [heps,hS]) hu
  have hrS := mul_le_mul_of_nonneg_right hr (hs.le.trans hS)
  have hNM := mul_le_mul_of_nonneg_left hM hN
  calc
    (A-a*S-H)/x+rho*S ≤ (2*eps*S-S^2/2)/x+rho*S := add_le_add hdiv le_rfl
    _ = (2*eps-S/2)*(S/x)+rho*S := by ring
    _ ≤ N*M-(s/4)*(S/x) := by linarith only [hdamp,hrS,hNM]

end MultiConsumerPermanence
