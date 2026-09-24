import proofs.RandomViability.BasalEnvelope
import proofs.RandomViability.CollectiveGrowth

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

/-- Actual nonfood occupied mass, not catalog size. -/
def nonfoodMass {n : ℕ} (x : Molecule n → ℝ) : ℝ :=
  ∑ z, if 2 < molLength z then (molLength z : ℝ)*x z else 0

/-- Paired passive mass-action speed with the literal selected catalyst rows. -/
def collectivePairSpeed {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → ℝ) (cat : Reaction n → Molecule n → ℝ)
    (x : Molecule n → ℝ) (r : Reaction n) : ℝ :=
  basal r + ∑ z, if r ∈ c z then cat r z*x z else 0

theorem collective_pair_speed_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → ℝ) (cat : Reaction n → Molecule n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z) (eps : ℝ)
    (hb : ∀ r, basal r ≤ 4*eps) (ha : ∀ r z, cat r z ≤ 16)
    (hfood : ∀ z, molLength z ≤ 2 → c z = ∅) (r : Reaction n) :
    collectivePairSpeed c basal cat x r ≤ 4*eps+(16/3)*nonfoodMass x := by
  have hsum : (∑ z, if r ∈ c z then cat r z*x z else 0) ≤
      (16/3)*nonfoodMass x := by
    unfold nonfoodMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    by_cases hl : 2 < molLength z
    · rw [if_pos hl]
      have hlen : (3 : ℝ) ≤ molLength z := by exact_mod_cast hl
      have hrate := mul_le_mul_of_nonneg_right (ha r z) (hx z)
      have hmass := mul_le_mul_of_nonneg_right hlen (hx z)
      split_ifs <;> nlinarith [hx z]
    · have hc : c z = ∅ := hfood z (by omega)
      simp [hc, hl]
  unfold collectivePairSpeed
  linarith [hb r]

/-- Total losses count both ordered substrate positions, including repeats. -/
def collectiveLoss {n : ℕ} (speed : Reaction n → ℝ)
    (x : Molecule n → ℝ) (z : Molecule n) : ℝ :=
  (∑ r, (if reactionLeft r = z then speed r*x (reactionLeft r)*x (reactionRight r) else 0)) +
  (∑ r, (if reactionRight r = z then speed r*x (reactionLeft r)*x (reactionRight r) else 0)) +
  (∑ r, (if reactionProduct r = z then speed r*x (reactionProduct r) else 0))

theorem collective_loss_bound {n : ℕ} (speed : Reaction n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z)
    (C : ℝ) (hC : 0 ≤ C) (hs : ∀ r, speed r ≤ C) (z : Molecule n) :
    collectiveLoss speed x z ≤ (2*polymerMass x+(molLength z-1))*C*x z := by
  have hleft : (∑ r : Reaction n, if reactionLeft r = z then
      speed r*x (reactionLeft r)*x (reactionRight r) else 0) ≤ C*x z*polymerMass x := by
    calc
      _ ≤ ∑ r : Reaction n, if reactionLeft r = z then C*x (reactionLeft r)*x (reactionRight r) else 0 := by
        apply Finset.sum_le_sum
        intro r _
        split_ifs
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hs r) (hx _)) (hx _)
        · exact le_rfl
      _ ≤ ∑ u, ∑ w, if u = z then C*x u*x w else 0 := by
        apply reaction_sum_le_ordered_pairs (fun u w => if u = z then C*x u*x w else 0)
        intro u w
        split_ifs
        · exact mul_nonneg (mul_nonneg hC (hx u)) (hx w)
        · exact le_rfl
      _ = C*x z*(∑ w, x w) := by simp [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (concentration_le_mass x hx) (mul_nonneg hC (hx z))
  have hright : (∑ r : Reaction n, if reactionRight r = z then
      speed r*x (reactionLeft r)*x (reactionRight r) else 0) ≤ C*x z*polymerMass x := by
    calc
      _ ≤ ∑ r : Reaction n, if reactionRight r = z then C*x (reactionLeft r)*x (reactionRight r) else 0 := by
        apply Finset.sum_le_sum
        intro r _
        split_ifs
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hs r) (hx _)) (hx _)
        · exact le_rfl
      _ ≤ ∑ u, ∑ w, if w = z then C*x u*x w else 0 := by
        apply reaction_sum_le_ordered_pairs (fun u w => if w = z then C*x u*x w else 0)
        intro u w
        split_ifs
        · exact mul_nonneg (mul_nonneg hC (hx u)) (hx w)
        · exact le_rfl
      _ = C*x z*(∑ u, x u) := by simp [← Finset.sum_mul, ← Finset.mul_sum]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (concentration_le_mass x hx) (mul_nonneg hC (hx z))
  have hrev : (∑ r : Reaction n, if reactionProduct r = z then
      speed r*x (reactionProduct r) else 0) ≤ (molLength z-1)*C*x z := by
    calc
      _ ≤ ∑ r : Reaction n, if reactionProduct r = z then C*x (reactionProduct r) else 0 := by
        apply Finset.sum_le_sum
        intro r _
        split_ifs
        · exact mul_le_mul_of_nonneg_right (hs r) (hx _)
        · exact le_rfl
      _ = ∑ y : Molecule n, (y.1.val : ℝ)*(if y = z then C*x y else 0) :=
        reaction_product_sum (fun y => if y = z then C*x y else 0)
      _ = _ := by simp [mul_ite, molLength]; ring
  unfold collectiveLoss
  nlinarith

end
end RandomViability
