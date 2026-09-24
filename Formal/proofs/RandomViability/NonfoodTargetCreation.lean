import proofs.RandomViability.FixedTargetCreationBound
import proofs.RandomViability.CollectiveDrift

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 70000

theorem nonmonomer_pair_mass_bound {n : ℕ} (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q) :
    3*(∑ u,∑ v,if 2 < molLength u+molLength v then x u*x v else 0) ≤ (polymerMass x)^2 := by
  let A := ∑ q,if molLength q = 1 then x q else 0
  let Q := ∑ q,x q
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun q _ => hx q)
  have hA : A ≤ Q := Finset.sum_le_sum (fun q _ => by split_ifs; exact le_rfl; exact hx q)
  have hmass : 2*Q-A ≤ polymerMass x := by
    unfold Q A polymerMass
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro q _
    by_cases hq : molLength q = 1
    · simp only [hq,↓reduceIte,Nat.cast_one,one_mul]
      linarith
    · have hh : (2 : ℝ) ≤ molLength q := by
        have hp : 1 ≤ molLength q := by simp [molLength]
        exact_mod_cast (show 2 ≤ molLength q by omega)
      simp only [hq,↓reduceIte,sub_zero]
      exact mul_le_mul_of_nonneg_right hh (hx q)
  have hpair (u v : Molecule n) :
      (if 2 < molLength u+molLength v then x u*x v else 0) =
        x u*x v-(if molLength u = 1 then x u else 0)*(if molLength v = 1 then x v else 0) := by
    have hu : 1 ≤ molLength u := by simp [molLength]
    have hv : 1 ≤ molLength v := by simp [molLength]
    by_cases ha : molLength u = 1 <;> by_cases hb : molLength v = 1
    · simp [ha,hb]
    · simp only [ha,hb,↓reduceIte,mul_zero,sub_zero,if_pos (by omega : 2 < 1+molLength v)]
    · simp only [ha,hb,↓reduceIte,zero_mul,sub_zero,if_pos (by omega : 2 < molLength u+1)]
    · simp only [ha,hb,↓reduceIte,zero_mul,sub_zero,if_pos (by omega : 2 < molLength u+molLength v)]
  have he : (∑ u,∑ v,if 2 < molLength u+molLength v then x u*x v else 0) = Q^2-A^2 := by
    simp_rw [hpair]
    simp only [Finset.sum_sub_distrib]
    rw [← Finset.sum_mul_sum,← Finset.sum_mul_sum]
    dsimp [Q,A]
    ring
  rw [he]
  have hnonneg : 0 ≤ 2*Q-A := by linarith
  have hs := pow_le_pow_left₀ hnonneg hmass 2
  nlinarith only [hs,sq_nonneg (Q-2*A)]

theorem fixed_nonfood_forward_creation {n : ℕ} (z : Molecule n) (hz : 2 < molLength z)
    (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q) :
    3*(∑ r : Reaction n,if reactionProduct r = z then x (reactionLeft r)*x (reactionRight r) else 0) ≤
      (polymerMass x)^2 := by
  have hb : (∑ r : Reaction n,if reactionProduct r = z then x (reactionLeft r)*x (reactionRight r) else 0) ≤
      ∑ u,∑ v,if 2 < molLength u+molLength v then x u*x v else 0 := by
    calc
      _ ≤ ∑ r : Reaction n,if 2 < molLength (reactionLeft r)+molLength (reactionRight r) then
          x (reactionLeft r)*x (reactionRight r) else 0 := by
        apply Finset.sum_le_sum
        intro r _
        by_cases hp : reactionProduct r = z
        · have hlen : molLength (reactionLeft r)+molLength (reactionRight r) = molLength z := by
            rw [← hp]
            simpa only [molLength_reactionLeft,molLength_reactionRight,molLength_reactionProduct] using reaction_length_add r
          simp only [hp,↓reduceIte,hlen,if_pos hz,le_refl]
        · simp only [hp,↓reduceIte]
          split_ifs
          · exact mul_nonneg (hx _) (hx _)
          · exact le_rfl
      _ ≤ _ := reaction_sum_le_ordered_pairs
        (fun u v : Molecule n => if 2 < molLength u+molLength v then x u*x v else 0)
        (fun u v => by dsimp only; split_ifs; exact mul_nonneg (hx u) (hx v); exact le_rfl)
  have hh := nonmonomer_pair_mass_bound x hx
  linarith only [hb,hh]

theorem long_concentration_successor_mass_bound {n k : ℕ} (x : Molecule n → ℝ)
    (hx : ∀ q,0 ≤ x q) :
    ((k : ℝ)+1)*(∑ q,longConcentration k x q) ≤ polymerMass x := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  unfold longConcentration
  split_ifs with h
  · apply mul_le_mul_of_nonneg_right _ (hx q)
    exact_mod_cast (show k+1 ≤ molLength q by omega)
  · simp only [mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (hx q)

theorem fixed_nonfood_cleavage_creation {n : ℕ} (z : Molecule n) (hz : 2 < molLength z)
    (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q) :
    2*((∑ r : Reaction n,if reactionLeft r = z then x (reactionProduct r) else 0)+
      (∑ r : Reaction n,if reactionRight r = z then x (reactionProduct r) else 0)) ≤ polymerMass x := by
  have hlen (r : Reaction n) (h : reactionLeft r = z ∨ reactionRight r = z) : 3 < molLength (reactionProduct r) := by
    have he : molLength (reactionLeft r)+molLength (reactionRight r) = molLength (reactionProduct r) := by
      simpa only [molLength_reactionLeft,molLength_reactionRight,molLength_reactionProduct] using reaction_length_add r
    have hl : 1 ≤ molLength (reactionLeft r) := by simp [molLength]
    have hr : 1 ≤ molLength (reactionRight r) := by simp [molLength]
    rcases h with h|h <;> rw [h] at he <;> omega
  have hleft : (∑ r : Reaction n,if reactionLeft r = z then x (reactionProduct r) else 0) =
      ∑ r : Reaction n,if reactionLeft r = z then longConcentration 3 x (reactionProduct r) else 0 := by
    apply Finset.sum_congr rfl
    intro r _
    by_cases he : reactionLeft r = z
    · simp only [he,↓reduceIte,longConcentration,if_pos (hlen r (Or.inl he))]
    · simp only [he,↓reduceIte]
  have hright : (∑ r : Reaction n,if reactionRight r = z then x (reactionProduct r) else 0) =
      ∑ r : Reaction n,if reactionRight r = z then longConcentration 3 x (reactionProduct r) else 0 := by
    apply Finset.sum_congr rfl
    intro r _
    by_cases he : reactionRight r = z
    · simp only [he,↓reduceIte,longConcentration,if_pos (hlen r (Or.inr he))]
    · simp only [he,↓reduceIte]
  rw [hleft,hright]
  have hh := fixed_target_cleavage_bound z (longConcentration 3 x) (longConcentration_nonneg 3 x hx)
  have hm := long_concentration_successor_mass_bound (k := 3) x hx
  norm_num at hm
  linarith only [hh,hm]

end
end RandomViability
