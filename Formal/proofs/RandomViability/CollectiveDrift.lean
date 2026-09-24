import proofs.RandomViability.CollectiveHost

set_option maxHeartbeats 20000

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

def collectiveGain {n : ℕ} (speed : Reaction n → ℝ)
    (x : Molecule n → ℝ) (z : Molecule n) : ℝ :=
  (∑ r, if reactionProduct r = z then speed r*x (reactionLeft r)*x (reactionRight r) else 0) +
  (∑ r, if reactionLeft r = z then speed r*x (reactionProduct r) else 0) +
  (∑ r, if reactionRight r = z then speed r*x (reactionProduct r) else 0)

/-- Full deterministic paired vector field, with unit food feed and turnover.
Every reaction contributes in both directions; passive catalysts cancel. -/
def collectiveDrift {n : ℕ} (speed : Reaction n → ℝ)
    (x : Molecule n → ℝ) (z : Molecule n) : ℝ :=
  (if molLength z ≤ 2 then 1 else 0)-x z+
    collectiveGain speed x z-collectiveLoss speed x z

theorem collective_gain_nonneg {n : ℕ} (speed : Reaction n → ℝ)
    (x : Molecule n → ℝ) (hs : ∀ r, 0 ≤ speed r) (hx : ∀ z, 0 ≤ x z)
    (z : Molecule n) : 0 ≤ collectiveGain speed x z := by
  unfold collectiveGain
  apply add_nonneg
  · apply add_nonneg
    · apply Finset.sum_nonneg
      intro r _
      split_ifs
      · exact mul_nonneg (mul_nonneg (hs r) (hx _)) (hx _)
      · exact le_rfl
    · apply Finset.sum_nonneg
      intro r _
      split_ifs
      · exact mul_nonneg (hs r) (hx _)
      · exact le_rfl
  · apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact mul_nonneg (hs r) (hx _)
    · exact le_rfl

theorem collective_gain_target {n : ℕ} (speed : Reaction n → ℝ)
    (x : Molecule n → ℝ) (hs : ∀ r, 0 ≤ speed r) (hx : ∀ z, 0 ≤ x z)
    (r₀ : Reaction n) :
    speed r₀*x (reactionLeft r₀)*x (reactionRight r₀) ≤
      collectiveGain speed x (reactionProduct r₀) := by
  have hf : speed r₀*x (reactionLeft r₀)*x (reactionRight r₀) ≤
      ∑ r, if reactionProduct r = reactionProduct r₀ then
        speed r*x (reactionLeft r)*x (reactionRight r) else 0 := by
    calc
      _ = (if reactionProduct r₀ = reactionProduct r₀ then
        speed r₀*x (reactionLeft r₀)*x (reactionRight r₀) else 0) := by simp
      _ ≤ _ := Finset.single_le_sum (f := fun r : Reaction n =>
        if reactionProduct r = reactionProduct r₀ then speed r*x (reactionLeft r)*x (reactionRight r) else 0) (fun r _ => by
        dsimp only
        split_ifs
        · exact mul_nonneg (mul_nonneg (hs r) (hx _)) (hx _)
        · exact le_rfl) (Finset.mem_univ r₀)
  have hl : 0 ≤ ∑ r, if reactionLeft r = reactionProduct r₀ then speed r*x (reactionProduct r) else 0 :=
    Finset.sum_nonneg (fun r _ => by split_ifs; exact mul_nonneg (hs r) (hx _); exact le_rfl)
  have hr : 0 ≤ ∑ r, if reactionRight r = reactionProduct r₀ then speed r*x (reactionProduct r) else 0 :=
    Finset.sum_nonneg (fun r _ => by split_ifs; exact mul_nonneg (hs r) (hx _); exact le_rfl)
  unfold collectiveGain
  linarith

theorem collective_food_drift {n : ℕ} (speed : Reaction n → ℝ)
    (x : Molecule n → ℝ) (hs0 : ∀ r, 0 ≤ speed r) (hx : ∀ z, 0 ≤ x z)
    (C : ℝ) (hC : 0 ≤ C) (hs : ∀ r, speed r ≤ C)
    (hL : polymerMass x ≤ 11) (z : Molecule n) (hz : molLength z = 2) :
    1-x z-23*C*x z ≤ collectiveDrift speed x z := by
  have hl := collective_loss_bound speed x hx C hC hs z
  have hg := collective_gain_nonneg speed x hs0 hx z
  have hm := mul_le_mul_of_nonneg_right hL (mul_nonneg hC (hx z))
  have hlen : (molLength z : ℝ) = 2 := by exact_mod_cast hz
  rw [hlen] at hl
  unfold collectiveDrift
  rw [if_pos (by omega)]
  linarith only [hl, hg, hm]

theorem collective_product_drift {n : ℕ} (speed : Reaction n → ℝ)
    (x : Molecule n → ℝ) (hs0 : ∀ r, 0 ≤ speed r) (hx : ∀ z, 0 ≤ x z)
    (C : ℝ) (hC : 0 ≤ C) (hs : ∀ r, speed r ≤ C)
    (hL : polymerMass x ≤ 11) (r : Reaction n)
    (hz : molLength (reactionProduct r) = 4) (eps : ℝ)
    (htarget : eps+4*x (reactionProduct r) ≤ speed r) :
    eps*x (reactionLeft r)*x (reactionRight r)+x (reactionProduct r)*
      (4*x (reactionLeft r)*x (reactionRight r)-1-25*C) ≤
      collectiveDrift speed x (reactionProduct r) := by
  have hl := collective_loss_bound speed x hx C hC hs (reactionProduct r)
  have hg := collective_gain_target speed x hs0 hx r
  have ht := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right htarget (hx (reactionLeft r))) (hx (reactionRight r))
  have hm := mul_le_mul_of_nonneg_right hL (mul_nonneg hC (hx (reactionProduct r)))
  have hlen : (molLength (reactionProduct r) : ℝ) = 4 := by exact_mod_cast hz
  rw [hlen] at hl
  unfold collectiveDrift
  rw [if_neg (by omega)]
  linarith only [hl, hg, ht, hm]

end
end RandomViability
