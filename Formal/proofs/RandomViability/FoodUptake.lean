import proofs.RandomViability.ShortIncidence
import proofs.PowerLawSmallRAF.ReversibleExplorationStructure

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

def foodMassWeight {n : ℕ} (x : Molecule n) : ℝ :=
  if molLength x ≤ 2 then molLength x else 0

def longConcentration {n : ℕ} (k : ℕ) (x : Molecule n → ℝ) (z : Molecule n) : ℝ :=
  if k < molLength z then x z else 0

def polymerMass {n : ℕ} (x : Molecule n → ℝ) : ℝ := ∑ z, (molLength z : ℝ) * x z

theorem foodMassWeight_nonneg {n : ℕ} (z : Molecule n) : 0 ≤ foodMassWeight z := by
  unfold foodMassWeight
  split_ifs <;> positivity

theorem longConcentration_nonneg {n : ℕ} (k : ℕ) (x : Molecule n → ℝ)
    (hx : ∀ z, 0 ≤ x z) (z : Molecule n) : 0 ≤ longConcentration k x z := by
  unfold longConcentration
  split_ifs <;> first | exact hx z | exact le_rfl

/-- The split-position sampler has no duplicate ordered ligation inputs. -/
theorem reaction_sum_le_ordered_pairs {n : ℕ} (f : Molecule n → Molecule n → ℝ)
    (hf : ∀ u w, 0 ≤ f u w) :
    (∑ r : Reaction n, f (reactionLeft r) (reactionRight r)) ≤ ∑ u, ∑ w, f u w := by
  let e : Reaction n → Molecule n × Molecule n := fun r => (reactionLeft r, reactionRight r)
  have he : Function.Injective e := by
    intro r s h
    exact binaryReaction_eq_of_left_eq_of_right_eq (congrArg Prod.fst h) (congrArg Prod.snd h)
  calc
    _ = ∑ p ∈ Finset.univ.image e, f p.1 p.2 := by
      rw [Finset.sum_image]
      exact fun r _ s _ h => he h
    _ ≤ ∑ p : Molecule n × Molecule n, f p.1 p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun p _ _ => hf p.1 p.2)
    _ = _ := Fintype.sum_prod_type _

theorem concentration_le_mass {n : ℕ} (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z) :
    (∑ z, x z) ≤ polymerMass x := by
  apply Finset.sum_le_sum
  intro z _
  have hl : (1 : ℝ) ≤ molLength z := by
    have h : 1 ≤ molLength z := by simp [molLength]
    exact_mod_cast h
  simpa using mul_le_mul_of_nonneg_right hl (hx z)

theorem food_concentration_mass_le {n : ℕ} (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z) :
    (∑ z, foodMassWeight z * x z) ≤ polymerMass x := by
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_right _ (hx z)
  unfold foodMassWeight
  split_ifs <;> first | exact le_rfl | positivity

theorem long_concentration_mass_bound {n : ℕ} (k : ℕ) (x : Molecule n → ℝ)
    (hx : ∀ z, 0 ≤ x z) :
    (k : ℝ) * (∑ z, longConcentration k x z) ≤ polymerMass x := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  unfold longConcentration
  split_ifs with h
  · apply mul_le_mul_of_nonneg_right _ (hx z)
    exact_mod_cast h.le
  · simp only [mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (hx z)

/-- Channel-level domination retaining the actual selected pair and catalyst.
This is the left-food contribution to the molecular-count envelope. -/
theorem selected_left_food_bound {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ ShortIncidence k c) (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z)
    (r : Reaction n) (z : Molecule n) :
    (if r ∈ c z then foodMassWeight (reactionLeft r) * x z * x (reactionLeft r) * x (reactionRight r) else 0) ≤
      foodMassWeight (reactionLeft r) * longConcentration k x z * x (reactionLeft r) * x (reactionRight r) +
      foodMassWeight (reactionLeft r) * x z * x (reactionLeft r) * longConcentration k x (reactionRight r) := by
  have hf := foodMassWeight_nonneg (reactionLeft r)
  have hz := longConcentration_nonneg k x hx z
  have hw := longConcentration_nonneg k x hx (reactionRight r)
  have hfirst : 0 ≤ foodMassWeight (reactionLeft r) * longConcentration k x z * x (reactionLeft r) * x (reactionRight r) :=
    mul_nonneg (mul_nonneg (mul_nonneg hf hz) (hx _)) (hx _)
  have hsecond : 0 ≤ foodMassWeight (reactionLeft r) * x z * x (reactionLeft r) * longConcentration k x (reactionRight r) :=
    mul_nonneg (mul_nonneg (mul_nonneg hf (hx _)) (hx _)) hw
  by_cases hs : r ∈ c z
  · rw [if_pos hs]
    by_cases hfood : molLength (reactionLeft r) ≤ 2
    · rcases shortIncidence_free_left_food hgood r z hs hfood with hlong | hlong
      · rw [show longConcentration k x z = x z from if_pos hlong]
        exact le_add_of_nonneg_right hsecond
      · rw [show longConcentration k x (reactionRight r) = x (reactionRight r) from if_pos hlong]
        exact le_add_of_nonneg_left hfirst
    · have hzfood : foodMassWeight (reactionLeft r) = 0 := if_neg hfood
      rw [hzfood]
      simp only [zero_mul, zero_add, le_refl]
  · rw [if_neg hs]
    exact add_nonneg hfirst hsecond

theorem selected_right_food_bound {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ ShortIncidence k c) (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z)
    (r : Reaction n) (z : Molecule n) :
    (if r ∈ c z then foodMassWeight (reactionRight r) * x z * x (reactionRight r) * x (reactionLeft r) else 0) ≤
      foodMassWeight (reactionRight r) * longConcentration k x z * x (reactionRight r) * x (reactionLeft r) +
      foodMassWeight (reactionRight r) * x z * x (reactionRight r) * longConcentration k x (reactionLeft r) := by
  have hf := foodMassWeight_nonneg (reactionRight r)
  have hz := longConcentration_nonneg k x hx z
  have hw := longConcentration_nonneg k x hx (reactionLeft r)
  have hfirst : 0 ≤ foodMassWeight (reactionRight r) * longConcentration k x z * x (reactionRight r) * x (reactionLeft r) :=
    mul_nonneg (mul_nonneg (mul_nonneg hf hz) (hx _)) (hx _)
  have hsecond : 0 ≤ foodMassWeight (reactionRight r) * x z * x (reactionRight r) * longConcentration k x (reactionLeft r) :=
    mul_nonneg (mul_nonneg (mul_nonneg hf (hx _)) (hx _)) hw
  by_cases hs : r ∈ c z
  · rw [if_pos hs]
    by_cases hfood : molLength (reactionRight r) ≤ 2
    · rcases shortIncidence_free_right_food hgood r z hs hfood with hlong | hlong
      · rw [show longConcentration k x z = x z from if_pos hlong]
        exact le_add_of_nonneg_right hsecond
      · rw [show longConcentration k x (reactionLeft r) = x (reactionLeft r) from if_pos hlong]
        exact le_add_of_nonneg_left hfirst
    · have hzfood : foodMassWeight (reactionRight r) = 0 := if_neg hfood
      rw [hzfood]
      simp only [zero_mul, zero_add, le_refl]
  · rw [if_neg hs]
    exact add_nonneg hfirst hsecond

theorem food_pair_factor {n : ℕ} (x y : Molecule n → ℝ) (a b : ℝ) :
    (∑ u, ∑ w, (foodMassWeight u * a * x u * x w + foodMassWeight u * b * x u * y w)) =
      a * (∑ u, foodMassWeight u * x u) * (∑ w, x w) +
      b * (∑ u, foodMassWeight u * x u) * (∑ w, y w) := by
  have h1 : ∀ u w, foodMassWeight u * a * x u * x w = a * (foodMassWeight u * x u) * x w := by
    intros; ring
  have h2 : ∀ u w, foodMassWeight u * b * x u * y w = b * (foodMassWeight u * x u) * y w := by
    intros; ring
  simp_rw [h1, h2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]

theorem selected_left_food_sum {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ ShortIncidence k c) (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z)
    (z : Molecule n) :
    (∑ r : Reaction n, if r ∈ c z then foodMassWeight (reactionLeft r) * x z * x (reactionLeft r) * x (reactionRight r) else 0) ≤
      longConcentration k x z * (∑ u, foodMassWeight u * x u) * (∑ w, x w) +
      x z * (∑ u, foodMassWeight u * x u) * (∑ w, longConcentration k x w) := by
  calc
    _ ≤ ∑ r : Reaction n,
        (foodMassWeight (reactionLeft r) * longConcentration k x z * x (reactionLeft r) * x (reactionRight r) +
        foodMassWeight (reactionLeft r) * x z * x (reactionLeft r) * longConcentration k x (reactionRight r)) :=
      Finset.sum_le_sum (fun r _ => selected_left_food_bound c hgood x hx r z)
    _ ≤ ∑ u, ∑ w, (foodMassWeight u * longConcentration k x z * x u * x w +
        foodMassWeight u * x z * x u * longConcentration k x w) := by
      apply reaction_sum_le_ordered_pairs (fun u w =>
        foodMassWeight u * longConcentration k x z * x u * x w +
        foodMassWeight u * x z * x u * longConcentration k x w)
      intro u w
      exact add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (foodMassWeight_nonneg u)
          (longConcentration_nonneg k x hx z)) (hx u)) (hx w))
        (mul_nonneg (mul_nonneg (mul_nonneg (foodMassWeight_nonneg u) (hx z))
          (hx u)) (longConcentration_nonneg k x hx w))
    _ = _ := food_pair_factor x (longConcentration k x) _ _

theorem selected_right_food_sum {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ ShortIncidence k c) (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z)
    (z : Molecule n) :
    (∑ r : Reaction n, if r ∈ c z then foodMassWeight (reactionRight r) * x z * x (reactionRight r) * x (reactionLeft r) else 0) ≤
      longConcentration k x z * (∑ u, foodMassWeight u * x u) * (∑ w, x w) +
      x z * (∑ u, foodMassWeight u * x u) * (∑ w, longConcentration k x w) := by
  calc
    _ ≤ ∑ r : Reaction n,
        (foodMassWeight (reactionRight r) * longConcentration k x z * x (reactionRight r) * x (reactionLeft r) +
        foodMassWeight (reactionRight r) * x z * x (reactionRight r) * longConcentration k x (reactionLeft r)) :=
      Finset.sum_le_sum (fun r _ => selected_right_food_bound c hgood x hx r z)
    _ ≤ ∑ w, ∑ u, (foodMassWeight u * longConcentration k x z * x u * x w +
        foodMassWeight u * x z * x u * longConcentration k x w) := by
      apply reaction_sum_le_ordered_pairs (fun w u =>
        foodMassWeight u * longConcentration k x z * x u * x w +
        foodMassWeight u * x z * x u * longConcentration k x w)
      intro w u
      exact add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (foodMassWeight_nonneg u)
          (longConcentration_nonneg k x hx z)) (hx u)) (hx w))
        (mul_nonneg (mul_nonneg (mul_nonneg (foodMassWeight_nonneg u) (hx z))
          (hx u)) (longConcentration_nonneg k x hx w))
    _ = _ := by rw [Finset.sum_comm]; exact food_pair_factor x (longConcentration k x) _ _

def catalyticFoodEnvelope {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (x : Molecule n → ℝ) : ℝ :=
  ∑ z, ∑ r : Reaction n, if r ∈ c z then
    (foodMassWeight (reactionLeft r) + foodMassWeight (reactionRight r)) *
      x z * x (reactionLeft r) * x (reactionRight r) else 0

theorem catalyticFoodEnvelope_sum_bound {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ ShortIncidence k c) (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z) :
    catalyticFoodEnvelope c x ≤
      4 * (∑ z, longConcentration k x z) * (∑ u, foodMassWeight u * x u) * (∑ w, x w) := by
  have hs : ∀ z, (∑ r : Reaction n, if r ∈ c z then
      (foodMassWeight (reactionLeft r) + foodMassWeight (reactionRight r)) * x z * x (reactionLeft r) * x (reactionRight r) else 0) ≤
      2 * (longConcentration k x z * (∑ u, foodMassWeight u * x u) * (∑ w, x w) +
      x z * (∑ u, foodMassWeight u * x u) * (∑ w, longConcentration k x w)) := by
    intro z
    have hl := selected_left_food_sum c hgood x hx z
    have hr := selected_right_food_sum c hgood x hx z
    have he : (∑ r : Reaction n, if r ∈ c z then
        (foodMassWeight (reactionLeft r) + foodMassWeight (reactionRight r)) * x z * x (reactionLeft r) * x (reactionRight r) else 0) =
        (∑ r : Reaction n, if r ∈ c z then foodMassWeight (reactionLeft r) * x z * x (reactionLeft r) * x (reactionRight r) else 0) +
        (∑ r : Reaction n, if r ∈ c z then foodMassWeight (reactionRight r) * x z * x (reactionRight r) * x (reactionLeft r) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> ring
    rw [he]
    linarith
  calc
    _ ≤ ∑ z, 2 * (longConcentration k x z * (∑ u, foodMassWeight u * x u) * (∑ w, x w) +
        x z * (∑ u, foodMassWeight u * x u) * (∑ w, longConcentration k x w)) :=
      Finset.sum_le_sum (fun z _ => hs z)
    _ = _ := by
      simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

theorem catalyticFoodEnvelope_mass_bound {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ ShortIncidence k c) (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z) :
    (k : ℝ) * catalyticFoodEnvelope c x ≤ 4 * (polymerMass x)^3 := by
  have hQ : 0 ≤ ∑ z, x z := Finset.sum_nonneg (fun z _ => hx z)
  have hF : 0 ≤ ∑ z, foodMassWeight z * x z :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (foodMassWeight_nonneg z) (hx z))
  have hL : 0 ≤ polymerMass x := le_trans hQ (concentration_le_mass x hx)
  have hprod : (k : ℝ) * (∑ z, longConcentration k x z) *
      (∑ z, foodMassWeight z * x z) * (∑ z, x z) ≤ (polymerMass x)^3 := by
    calc
      _ ≤ polymerMass x * (∑ z, foodMassWeight z * x z) * (∑ z, x z) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (long_concentration_mass_bound k x hx) hF) hQ
      _ ≤ polymerMass x * polymerMass x * polymerMass x :=
        mul_le_mul (mul_le_mul_of_nonneg_left (food_concentration_mass_le x hx) hL)
          (concentration_le_mass x hx) hQ (mul_nonneg hL hL)
      _ = _ := by ring
  calc
    _ ≤ (k : ℝ) * (4 * (∑ z, longConcentration k x z) *
        (∑ z, foodMassWeight z * x z) * (∑ z, x z)) :=
      mul_le_mul_of_nonneg_left (catalyticFoodEnvelope_sum_bound c hgood x hx) (Nat.cast_nonneg k)
    _ = 4 * ((k : ℝ) * (∑ z, longConcentration k x z) *
        (∑ z, foodMassWeight z * x z) * (∑ z, x z)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by norm_num)

end
end RandomViability
