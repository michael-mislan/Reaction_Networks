import proofs.RandomViability.ShortTargetTailLoss
import proofs.RandomViability.FixedTargetCreationBound
import proofs.RandomViability.CollectiveDrift

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 80000

private theorem selected_parent_gain_bound {n K : ℕ} (f : Reaction n → Molecule n)
    (z : Molecule n) (speed : Reaction n → ℝ) (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q)
    (C : ℝ) (hC : 0 ≤ C) (hall : ∀ r,speed r ≤ C)
    (hshort : ∀ r,reactionProductLength r ≤ K+2 → (K : ℝ)*speed r ≤ C) :
    (K : ℝ)*(∑ r : Reaction n,if f r = z then speed r*x (reactionProduct r) else 0) ≤
      C*(∑ r : Reaction n,if f r = z then x (reactionProduct r) else 0)+
      (K : ℝ)*C*(∑ r : Reaction n,if f r = z then longConcentration K x (reactionProduct r) else 0) := by
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r _
  by_cases he : f r = z
  · simp only [he,↓reduceIte]
    by_cases hp : reactionProductLength r ≤ K+2
    · have hh := mul_le_mul_of_nonneg_right (hshort r hp) (hx (reactionProduct r))
      have hn := mul_nonneg (mul_nonneg (Nat.cast_nonneg K) hC)
        (longConcentration_nonneg K x hx (reactionProduct r))
      nlinarith only [hh,hn]
    · have hlong : K < molLength (reactionProduct r) := by
        rw [molLength_reactionProduct]
        omega
      rw [show longConcentration K x (reactionProduct r) = x (reactionProduct r) from if_pos hlong]
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hall r) (hx (reactionProduct r))) (Nat.cast_nonneg K)
      have hn := mul_nonneg hC (hx (reactionProduct r))
      nlinarith only [hh,hn]
  · simp only [he,↓reduceIte,mul_zero,zero_add,le_refl]

theorem short_target_gain_bound {n K : ℕ} (z : Molecule n) (hz : molLength z ≤ K+2)
    (speed : Reaction n → ℝ) (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q)
    (C : ℝ) (hC : 0 ≤ C) (hall : ∀ r,speed r ≤ C)
    (hshort : ∀ r,reactionProductLength r ≤ K+2 → (K : ℝ)*speed r ≤ C) :
    (K : ℝ)*collectiveGain speed x z ≤ C*(polymerMass x)^2+4*C*polymerMass x := by
  let Q := ∑ q,x q
  have hQ : Q ≤ polymerMass x := concentration_le_mass x hx
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun q _ => hx q)
  have hQ2 := pow_le_pow_left₀ hQ0 hQ 2
  have hforward : (K : ℝ)*(∑ r : Reaction n,if reactionProduct r = z then
      speed r*x (reactionLeft r)*x (reactionRight r) else 0) ≤ C*(polymerMass x)^2 := by
    calc
      _ ≤ C*(∑ r : Reaction n,x (reactionLeft r)*x (reactionRight r)) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro r _
        by_cases he : reactionProduct r = z
        · rw [if_pos he]
          have hp : reactionProductLength r ≤ K+2 := by
            have hh : reactionProductLength r = molLength z := congrArg molLength he
            omega
          have hh := mul_le_mul_of_nonneg_right (hshort r hp)
            (mul_nonneg (hx (reactionLeft r)) (hx (reactionRight r)))
          nlinarith only [hh]
        · rw [if_neg he,mul_zero]
          exact mul_nonneg hC (mul_nonneg (hx _) (hx _))
      _ ≤ C*(∑ u,∑ v,x u*x v) := mul_le_mul_of_nonneg_left
        (reaction_sum_le_ordered_pairs _ (fun u v => mul_nonneg (hx u) (hx v))) hC
      _ = C*Q^2 := by rw [← Finset.sum_mul_sum]; dsimp [Q]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ2 hC
  have hl := selected_parent_gain_bound reactionLeft z speed x hx C hC hall hshort
  have hr := selected_parent_gain_bound reactionRight z speed x hx C hC hall hshort
  have hplain := fixed_target_cleavage_bound z x hx
  have htail := fixed_target_cleavage_bound z (longConcentration K x) (longConcentration_nonneg K x hx)
  have htailM := long_concentration_mass_bound K x hx
  have hpC := mul_le_mul_of_nonneg_left hplain hC
  have hqC := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 2*C)
  have htC := mul_le_mul_of_nonneg_left htail (mul_nonneg (Nat.cast_nonneg K) hC)
  have htM := mul_le_mul_of_nonneg_left htailM (by positivity : 0 ≤ 2*C)
  unfold collectiveGain
  nlinarith only [hforward,hl,hr,hpC,hqC,htC,htM]

/-- Uniform catalytic creation of a short coordinate, with all nonlocal
incidences allowed. Applies to food as well as nonfood coordinates. -/
theorem short_free_target_catalytic_gain {n K : ℕ} (c : SourceMoleculeFibreConfig n)
    (hfree : ¬ShortIncidence K c) (cat : Reaction n → Molecule n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q)
    (κ : ℝ) (hκ : 0 ≤ κ) (hcat : ∀ r z,cat r z ≤ κ)
    (z : Molecule n) (hz : molLength z ≤ K+2) :
    (K : ℝ)*collectiveGain (collectivePairSpeed c (fun _ => 0) cat x) x z ≤
      κ*(polymerMass x)^3+4*κ*(polymerMass x)^2 := by
  have hL : 0 ≤ polymerMass x := Finset.sum_nonneg (fun q _ => mul_nonneg (Nat.cast_nonneg _) (hx q))
  have hh := short_target_gain_bound z hz (collectivePairSpeed c (fun _ => 0) cat x) x hx
    (κ*polymerMass x) (mul_nonneg hκ hL)
    (catalytic_pair_speed_mass_bound c cat x hx κ hκ hcat)
    (short_free_catalytic_pair_speed c hfree cat x hx κ hκ hcat)
  nlinarith only [hh]

end
end RandomViability
