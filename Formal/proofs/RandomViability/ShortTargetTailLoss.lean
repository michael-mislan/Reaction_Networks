import proofs.RandomViability.CollectiveHost

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 80000

theorem coordinate_mass_le {n : ℕ} (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q)
    (p : Molecule n) : (molLength p : ℝ)*x p ≤ polymerMass x :=
  Finset.single_le_sum (fun q _ => mul_nonneg (Nat.cast_nonneg _) (hx q)) (Finset.mem_univ p)

private theorem short_target_position_loss_bound {n k : ℕ}
    (first second : Reaction n → Molecule n)
    (hlen : ∀ r,molLength (first r)+molLength (second r) = reactionProductLength r)
    (hsum : ∀ f : Molecule n → Molecule n → ℝ,(∀ u v,0 ≤ f u v) →
      (∑ r : Reaction n,f (first r) (second r)) ≤ ∑ u,∑ v,f u v)
    (speed : Reaction n → ℝ) (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q)
    (C : ℝ) (hC : 0 ≤ C) (hall : ∀ r,speed r ≤ C)
    (hshort : ∀ r,reactionProductLength r ≤ 2*k+2 → (2*(k : ℝ))*speed r ≤ C)
    (p : Molecule n) (hp : molLength p ≤ k) (hp3 : 3 ≤ molLength p) :
    (2*(k : ℝ))*(∑ r : Reaction n,if first r = p then speed r*x (first r)*x (second r) else 0) ≤
      C*(polymerMass x)^2 := by
  let Q := ∑ q,x q
  let U := ∑ q,longConcentration k x q
  let L := polymerMass x
  have hL : 0 ≤ L := Finset.sum_nonneg (fun q _ => mul_nonneg (Nat.cast_nonneg _) (hx q))
  have hQ : Q ≤ L := concentration_le_mass x hx
  have hU : (k : ℝ)*U ≤ L := long_concentration_mass_bound k x hx
  have hpL : 3*x p ≤ L := by
    have hl : (3 : ℝ) ≤ molLength p := by exact_mod_cast hp3
    exact (mul_le_mul_of_nonneg_right hl (hx p)).trans (coordinate_mass_le x hx p)
  let F : Molecule n → Molecule n → ℝ := fun u v =>
    if u = p then C*x u*x v+(2*(k : ℝ))*C*x u*longConcentration k x v else 0
  have hF : ∀ u v,0 ≤ F u v := by
    intro u v
    dsimp [F]
    split_ifs
    · exact add_nonneg (mul_nonneg (mul_nonneg hC (hx u)) (hx v))
        (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC) (hx u))
          (longConcentration_nonneg k x hx v))
    · exact le_rfl
  have hpoint (r : Reaction n) :
      (2*(k : ℝ))*(if first r = p then speed r*x (first r)*x (second r) else 0) ≤
        F (first r) (second r) := by
    by_cases hf : first r = p
    · simp only [F,hf,↓reduceIte]
      by_cases ht : k < molLength (second r)
      · rw [show longConcentration k x (second r) = x (second r) from if_pos ht]
        have hb := mul_le_mul_of_nonneg_right (hall r) (mul_nonneg (hx p) (hx (second r)))
        have hb' := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*(k : ℝ))
        have hn := mul_nonneg (mul_nonneg hC (hx p)) (hx (second r))
        nlinarith only [hb',hn]
      · rw [show longConcentration k x (second r) = 0 from if_neg ht]
        have hprod : reactionProductLength r ≤ 2*k+2 := by
          have he := hlen r
          rw [hf] at he
          omega
        have hb := mul_le_mul_of_nonneg_right (hshort r hprod) (mul_nonneg (hx p) (hx (second r)))
        nlinarith only [hb]
    · simp only [F,hf,↓reduceIte,mul_zero,le_refl]
  have htotal : (2*(k : ℝ))*(∑ r : Reaction n,
      if first r = p then speed r*x (first r)*x (second r) else 0) ≤
      C*x p*Q+(2*(k : ℝ))*C*x p*U := by
    calc
      _ = ∑ r : Reaction n,(2*(k : ℝ))*(if first r = p then speed r*x (first r)*x (second r) else 0) :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ r : Reaction n,F (first r) (second r) := Finset.sum_le_sum (fun r _ => hpoint r)
      _ ≤ ∑ u,∑ v,F u v := hsum F hF
      _ = _ := by simp [F,Q,U,Finset.sum_add_distrib,← Finset.mul_sum]
  have hfirst := mul_le_mul_of_nonneg_left hQ (mul_nonneg hC (hx p))
  have hsecond := mul_le_mul_of_nonneg_left hU
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) (hx p))
  have hlast := mul_le_mul_of_nonneg_left hpL (mul_nonneg hC hL)
  change _ ≤ C*L^2
  nlinarith only [htotal,hfirst,hsecond,hlast]

/-- Two-scale catalytic loss estimate. A short product has a small coefficient;
a large coefficient can consume the short target only with a long partner. -/
theorem short_target_loss_bound {n k : ℕ}
    (speed : Reaction n → ℝ) (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q)
    (C : ℝ) (hC : 0 ≤ C) (hall : ∀ r,speed r ≤ C)
    (hshort : ∀ r,reactionProductLength r ≤ 2*k+2 → (2*(k : ℝ))*speed r ≤ C)
    (p : Molecule n) (hp : molLength p ≤ k) (hp3 : 3 ≤ molLength p) :
    (2*(k : ℝ))*collectiveLoss speed x p ≤ C*polymerMass x+2*C*(polymerMass x)^2 := by
  have hl := short_target_position_loss_bound reactionLeft reactionRight
    (fun r => by simpa only [molLength_reactionLeft,molLength_reactionRight] using reaction_length_add r)
    (fun f hf => reaction_sum_le_ordered_pairs f hf) speed x hx C hC hall hshort p hp hp3
  have hr := short_target_position_loss_bound reactionRight reactionLeft
    (fun r => by simpa only [molLength_reactionLeft,molLength_reactionRight,Nat.add_comm] using reaction_length_add r)
    (fun f hf => by
      have hh := reaction_sum_le_ordered_pairs (fun u v => f v u) (fun u v => hf v u)
      rw [Finset.sum_comm] at hh
      exact hh) speed x hx C hC hall hshort p hp hp3
  have hpL := coordinate_mass_le x hx p
  have hpC := mul_le_mul_of_nonneg_left hpL hC
  have hcleave : (2*(k : ℝ))*(∑ r : Reaction n,
      if reactionProduct r = p then speed r*x (reactionProduct r) else 0) ≤ C*polymerMass x := by
    calc
      _ = ∑ r : Reaction n,(2*(k : ℝ))*(if reactionProduct r = p then speed r*x (reactionProduct r) else 0) :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ r : Reaction n,if reactionProduct r = p then C*x (reactionProduct r) else 0 := by
        apply Finset.sum_le_sum
        intro r _
        by_cases he : reactionProduct r = p
        · simp only [he,↓reduceIte]
          have hprod : reactionProductLength r ≤ 2*k+2 := by
            have hlen : reactionProductLength r = molLength p := congrArg molLength he
            omega
          have hb := mul_le_mul_of_nonneg_right (hshort r hprod) (hx p)
          nlinarith only [hb]
        · simp only [he,↓reduceIte,mul_zero,le_refl]
      _ = ∑ q : Molecule n,(q.1.val : ℝ)*(if q = p then C*x q else 0) :=
        reaction_product_sum (fun q => if q = p then C*x q else 0)
      _ = (molLength p-1 : ℝ)*C*x p := by simp [mul_ite,molLength]; ring
      _ ≤ _ := by nlinarith only [hpC,mul_nonneg hC (hx p)]
  have hrEq : (∑ r : Reaction n,if reactionRight r = p then speed r*x (reactionRight r)*x (reactionLeft r) else 0) =
      ∑ r : Reaction n,if reactionRight r = p then speed r*x (reactionLeft r)*x (reactionRight r) else 0 := by
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> ring
  rw [hrEq] at hr
  unfold collectiveLoss
  nlinarith only [hl,hr,hcleave]

theorem catalytic_pair_speed_mass_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (cat : Reaction n → Molecule n → ℝ) (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q)
    (κ : ℝ) (hκ : 0 ≤ κ) (hcat : ∀ r z,cat r z ≤ κ) (r : Reaction n) :
    collectivePairSpeed c (fun _ => 0) cat x r ≤ κ*polymerMass x := by
  unfold collectivePairSpeed
  simp only [zero_add]
  calc
    _ ≤ ∑ z,κ*x z := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs
      · exact mul_le_mul_of_nonneg_right (hcat r z) (hx z)
      · exact mul_nonneg hκ (hx z)
    _ = κ*(∑ z,x z) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (concentration_le_mass x hx) hκ

theorem short_free_catalytic_pair_speed {n K : ℕ} (c : SourceMoleculeFibreConfig n)
    (hfree : ¬ShortIncidence K c) (cat : Reaction n → Molecule n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q)
    (κ : ℝ) (hκ : 0 ≤ κ) (hcat : ∀ r z,cat r z ≤ κ)
    (r : Reaction n) (hr : reactionProductLength r ≤ K+2) :
    (K : ℝ)*collectivePairSpeed c (fun _ => 0) cat x r ≤ κ*polymerMass x := by
  have htail : collectivePairSpeed c (fun _ => 0) cat x r ≤ κ*∑ z,longConcentration K x z := by
    unfold collectivePairSpeed
    simp only [zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    by_cases hs : r ∈ c z
    · rw [if_pos hs]
      have hz : K < molLength z := by
        by_contra hh
        apply hfree
        exact ⟨z,by simp only [binaryFood,Finset.mem_filter,Finset.mem_univ,true_and]; omega,r,hr,hs⟩
      rw [show longConcentration K x z = x z from if_pos hz]
      exact mul_le_mul_of_nonneg_right (hcat r z) (hx z)
    · rw [if_neg hs]
      exact mul_nonneg hκ (longConcentration_nonneg K x hx z)
  calc
    _ ≤ (K : ℝ)*(κ*∑ z,longConcentration K x z) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg K)
    _ = κ*((K : ℝ)*∑ z,longConcentration K x z) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (long_concentration_mass_bound K x hx) hκ

/-- Uniform short-target loss for an arbitrary host with no local incidence.
The host may saturate every incidence outside the cutoff. -/
theorem short_free_target_catalytic_loss {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (hfree : ¬ShortIncidence (2*k) c) (cat : Reaction n → Molecule n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q)
    (κ : ℝ) (hκ : 0 ≤ κ) (hcat : ∀ r z,cat r z ≤ κ)
    (p : Molecule n) (hp : molLength p ≤ k) (hp3 : 3 ≤ molLength p) :
    (2*(k : ℝ))*collectiveLoss (collectivePairSpeed c (fun _ => 0) cat x) x p ≤
      κ*(polymerMass x)^2+2*κ*(polymerMass x)^3 := by
  have hL : 0 ≤ polymerMass x := Finset.sum_nonneg (fun q _ => mul_nonneg (Nat.cast_nonneg _) (hx q))
  have hs : ∀ r,reactionProductLength r ≤ 2*k+2 →
      (2*(k : ℝ))*collectivePairSpeed c (fun _ => 0) cat x r ≤ κ*polymerMass x := by
    intro r hr
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      short_free_catalytic_pair_speed c hfree cat x hx κ hκ hcat r hr
  have hh := short_target_loss_bound (collectivePairSpeed c (fun _ => 0) cat x) x hx
    (κ*polymerMass x) (mul_nonneg hκ hL)
    (catalytic_pair_speed_mass_bound c cat x hx κ hκ hcat) hs p hp hp3
  nlinarith only [hh]

end
end RandomViability
