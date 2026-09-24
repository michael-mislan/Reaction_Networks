import proofs.StartupMarked.RetainedReward
import proofs.RandomViability.PhysicalSelectedFlux

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem two_dimer_product_bound {n : ℕ} (x : Molecule n → ℝ)
    (hx : ∀ z,0 ≤ x z) (hM : polymerMass x ≤ 11) (u w : Molecule n)
    (huw : u ≠ w) (hu : molLength u = 2) (hw : molLength w = 2) :
    x u*x w ≤ 121/16 := by
  have hs : (∑ z ∈ ({u,w} : Finset (Molecule n)),(molLength z : ℝ)*x z) ≤ polymerMass x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro z _ _
    exact mul_nonneg (Nat.cast_nonneg _) (hx z)
  have hh : 2*x u+2*x w ≤ 11 := by
    have hh := hs.trans hM
    simpa [huw,hu,hw] using hh
  have hsum : x u+x w ≤ (11/2 : ℝ) := by linarith
  have hsq := pow_le_pow_left₀ (add_nonneg (hx u) (hx w)) hsum 2
  nlinarith [sq_nonneg (x u-x w)]

theorem selected_forward_rate_le {n : ℕ} (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hc : (cat r (reactionProduct r) : ℝ) ≤ 16)
    (hM : (countMass N : ℝ) ≤ 11*V)
    (huw : reactionLeft r ≠ reactionRight r)
    (hu : molLength (reactionLeft r) = 2) (hw : molLength (reactionRight r) = 2) :
    unboundedPhysicalRate cfg V 1 basal cat N (selectedForward r) ≤ 121*(N (reactionProduct r) : ℝ) := by
  let x := fun z => (N z : ℝ)/(V : ℝ)
  have hm : polymerMass x ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).mpr hM
  have hprod := two_dimer_product_bound x (fun z => by dsimp [x]; positivity) hm _ _ huw hu hw
  have hr := unbounded_catalytic_ligation_rate_le cfg V 1 hV basal cat N r (reactionProduct r)
    16 (by norm_num) hc
  have he : 16*((N (reactionLeft r) : ℝ)*N (reactionRight r)*N (reactionProduct r))/(V : ℝ)^2 =
      16*(x (reactionLeft r)*x (reactionRight r))*(N (reactionProduct r) : ℝ) := by
    dsimp [x]
    ring
  rw [he] at hr
  have hp := mul_le_mul_of_nonneg_right hprod (show 0 ≤ 16*(N (reactionProduct r) : ℝ) by positivity)
  exact hr.trans (by nlinarith only [hp])

end
end StartupMarked
