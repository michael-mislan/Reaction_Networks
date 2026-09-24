import proofs.RandomViability.FoodUptake
import proofs.RandomViability.BoundedQuietComparison

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

theorem reaction_product_sum {n : ℕ} (x : Molecule n → ℝ) :
    (∑ r : Reaction n, x (reactionProduct r)) = ∑ z : Molecule n, (z.1.val : ℝ)*x z := by
  simp only [Reaction, Molecule, Fintype.sum_sigma, Fintype.sum_prod_type, reactionProduct]
  simp

theorem reaction_product_sum_le_mass {n : ℕ} (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z) :
    (∑ r : Reaction n, x (reactionProduct r)) ≤ polymerMass x := by
  rw [reaction_product_sum]
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_right _ (hx z)
  simp [molLength]

theorem basal_factorial_product_le {n : ℕ} (N : Molecule n → ℕ) (u w : Molecule n) :
    (∏ x, ((N x).descFactorial (singleCount u x + singleCount w x) : ℝ)) ≤ (N u : ℝ)*N w := by
  calc
    _ ≤ ∏ x, (N x : ℝ)^(singleCount u x + singleCount w x) := by
      apply Finset.prod_le_prod
      · intro x _
        positivity
      · intro x _
        exact_mod_cast Nat.descFactorial_le_pow (N x) _
    _ = _ := by
      simp only [pow_add, Finset.prod_mul_distrib]
      simp [singleCount, apply_ite]

theorem bounded_basal_ligation_rate_le {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : BoundedCounts n B) (r : Reaction n) :
    (boundedPhysicalCountModel c V D basal cat).rate N (.inr (.inl (r,true))) ≤
      (basal r : ℝ)*((boundedCountsValue N (reactionLeft r) : ℝ)*boundedCountsValue N (reactionRight r))/V := by
  change (if ∀ x, physicalChannelInput (.inr (.inl (r,true))) x ≤ boundedCountsValue N x then
    physicalChannelRate c V D basal cat (boundedCountsValue N) (.inr (.inl (r,true))) else 0) ≤ _
  split_ifs
  · unfold physicalChannelRate
    have hi : (∑ x, physicalChannelInput (.inr (.inl (r,true))) x) = 2 := by
      simp [physicalChannelInput, singleCount, Finset.sum_add_distrib]
    rw [hi]
    simp only [physicalChannelCoefficient, physicalChannelInput, if_true]
    calc
      _ ≤ ((basal r : ℝ)*V)*((boundedCountsValue N (reactionLeft r) : ℝ)*boundedCountsValue N (reactionRight r))/(V : ℝ)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (basal_factorial_product_le (boundedCountsValue N) _ _) (by positivity)) (by positivity)
      _ = _ := by field_simp
  · positivity

theorem bounded_basal_cleavage_rate_le {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : BoundedCounts n B) (r : Reaction n) :
    (boundedPhysicalCountModel c V D basal cat).rate N (.inr (.inl (r,false))) ≤
      (basal r : ℝ)*boundedCountsValue N (reactionProduct r) := by
  change (if ∀ x, physicalChannelInput (.inr (.inl (r,false))) x ≤ boundedCountsValue N x then
    physicalChannelRate c V D basal cat (boundedCountsValue N) (.inr (.inl (r,false))) else 0) ≤ _
  split_ifs
  · unfold physicalChannelRate
    simp [physicalChannelCoefficient, physicalChannelInput, singleCount, apply_ite]
    field_simp
    exact le_rfl
  · positivity

theorem bounded_basal_intensity_mass_bound {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : BoundedCounts n B)
    (b : ℝ) (hb : 0 ≤ b) (hcap : ∀ r, (basal r : ℝ) ≤ b) :
    boundedBasalIntensity c V D basal cat N ≤
      b*((polymerMass (fun z => (boundedCountsValue N z : ℝ)))^2/V+
        polymerMass (fun z => (boundedCountsValue N z : ℝ))) := by
  let x : Molecule n → ℝ := fun z => boundedCountsValue N z
  have hx : ∀ z, 0 ≤ x z := fun z => Nat.cast_nonneg _
  have he : boundedBasalIntensity c V D basal cat N =
      ∑ r, ((boundedPhysicalCountModel c V D basal cat).rate N (.inr (.inl (r,false))) +
        (boundedPhysicalCountModel c V D basal cat).rate N (.inr (.inl (r,true)))) := by
    simp [boundedBasalIntensity, Fintype.sum_sum_type, Fintype.sum_prod_type, isBasalChannel]
    apply Finset.sum_congr rfl
    intro r _
    exact add_comm _ _
  have hf : (∑ r : Reaction n, x (reactionLeft r)*x (reactionRight r)) ≤ (polymerMass x)^2 := by
    have hh := reaction_sum_le_ordered_pairs (fun u w => x u*x w) (fun u w => mul_nonneg (hx u) (hx w))
    have hs : (∑ u, ∑ w, x u*x w) = (∑ u, x u)^2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    rw [hs] at hh
    have hm := concentration_le_mass x hx
    have hn : 0 ≤ ∑ u, x u := Finset.sum_nonneg (fun u _ => hx u)
    nlinarith
  have hr := reaction_product_sum_le_mass x hx
  rw [he]
  calc
    _ ≤ ∑ r : Reaction n, (b*x (reactionProduct r)+b*(x (reactionLeft r)*x (reactionRight r))/V) := by
      apply Finset.sum_le_sum
      intro r _
      apply add_le_add
      · exact (bounded_basal_cleavage_rate_le c V D hV basal cat N r).trans
          (mul_le_mul_of_nonneg_right (hcap r) (hx _))
      · exact (bounded_basal_ligation_rate_le c V D hV basal cat N r).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hcap r) (mul_nonneg (hx _) (hx _))) hV.le)
    _ = b*(∑ r : Reaction n, x (reactionProduct r)) +
        b*(∑ r : Reaction n, x (reactionLeft r)*x (reactionRight r))/V := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ b*polymerMass x + b*(polymerMass x)^2/V :=
      add_le_add (mul_le_mul_of_nonneg_left hr hb)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf hb) hV.le)
    _ = _ := by dsimp [x]; ring

end
end RandomViability
