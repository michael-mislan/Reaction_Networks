import proofs.RandomViability.CollectiveDrift

set_option maxHeartbeats 20000

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

def collectiveVectorField {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → ℝ) (cat : Reaction n → Molecule n → ℝ)
    (x : Molecule n → ℝ) : Molecule n → ℝ :=
  collectiveDrift (collectivePairSpeed c basal cat x) x

theorem collective_pair_speed_nonneg {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → ℝ) (cat : Reaction n → Molecule n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z)
    (hb : ∀ r, 0 ≤ basal r) (ha : ∀ r z, 0 ≤ cat r z) (r : Reaction n) :
    0 ≤ collectivePairSpeed c basal cat x r := by
  apply add_nonneg (hb r)
  apply Finset.sum_nonneg
  intro z _
  split_ifs
  · exact mul_nonneg (ha r z) (hx z)
  · exact le_rfl

theorem collective_pair_speed_target {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → ℝ) (cat : Reaction n → Molecule n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z)
    (ha : ∀ r z, 0 ≤ cat r z) (eps : ℝ) (r : Reaction n)
    (hb : eps ≤ basal r) (hc : 4 ≤ cat r (reactionProduct r))
    (hsel : r ∈ c (reactionProduct r)) :
    eps+4*x (reactionProduct r) ≤ collectivePairSpeed c basal cat x r := by
  have hsingle : cat r (reactionProduct r)*x (reactionProduct r) ≤
      ∑ z, if r ∈ c z then cat r z*x z else 0 := by
    calc
      _ = (if r ∈ c (reactionProduct r) then cat r (reactionProduct r)*x (reactionProduct r) else 0) := by rw [if_pos hsel]
      _ ≤ _ := Finset.single_le_sum (f := fun z : Molecule n =>
        if r ∈ c z then cat r z*x z else 0) (fun z _ => by
        dsimp only
        split_ifs
        · exact mul_nonneg (ha r z) (hx z)
        · exact le_rfl) (Finset.mem_univ _)
  have hrate := mul_le_mul_of_nonneg_right hc (hx (reactionProduct r))
  unfold collectivePairSpeed
  linarith

/-- Corrected-growth certificate under the actual source event, for the full
deterministic host. No competing nonfood assignment is excluded. -/
theorem collective_literal_corrected_growth {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → ℝ) (cat : Reaction n → Molecule n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z) (eps : ℝ) (heps : 0 ≤ eps)
    (hb : ∀ r, eps ≤ basal r ∧ basal r ≤ 4*eps)
    (ha : ∀ r z, 0 ≤ cat r z ∧ cat r z ≤ 16)
    (hfood : ∀ z, molLength z ≤ 2 → c z = ∅)
    (hL : polymerMass x ≤ 11) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hp : molLength (reactionProduct r) = 4)
    (hsel : r ∈ c (reactionProduct r)) (hcat : 4 ≤ cat r (reactionProduct r))
    (hpos : 0 < x (reactionProduct r)) :
    2-468*eps-624*nonfoodMass x ≤
      collectiveVectorField c basal cat x (reactionProduct r)/x (reactionProduct r) -
      4*(-2*foodDeficit (x (reactionLeft r))*collectiveVectorField c basal cat x (reactionLeft r)-
         2*foodDeficit (x (reactionRight r))*collectiveVectorField c basal cat x (reactionRight r)) := by
  let speed := collectivePairSpeed c basal cat x
  have hs0 : ∀ r, 0 ≤ speed r := collective_pair_speed_nonneg c basal cat x hx
    (fun r => heps.trans (hb r).1) (fun r z => (ha r z).1)
  have hs : ∀ r, speed r ≤ 4*eps+(16/3)*nonfoodMass x :=
    collective_pair_speed_bound c basal cat x hx eps (fun r => (hb r).2)
      (fun r z => (ha r z).2) hfood
  have hM : 0 ≤ nonfoodMass x := by
    apply Finset.sum_nonneg
    intro z _
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (hx z)
    · exact le_rfl
  have hC : 0 ≤ 4*eps+(16/3)*nonfoodMass x := by positivity
  have hu := collective_food_drift speed x hs0 hx _ hC hs hL (reactionLeft r) hl
  have hw := collective_food_drift speed x hs0 hx _ hC hs hL (reactionRight r) hr
  have ht := collective_pair_speed_target c basal cat x hx (fun r z => (ha r z).1)
    eps r (hb r).1 hcat hsel
  have hz := collective_product_drift speed x hs0 hx _ hC hs hL r hp eps ht
  exact collective_corrected_growth _ _ _ _ _ _ eps _ (hx _) (hx _) hpos heps hM hu hw hz

end
end RandomViability
