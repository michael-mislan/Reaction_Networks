import proofs.RandomViability.CollectiveCertificate

set_option maxHeartbeats 20000

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

theorem nonfoodMass_le_mass {n : ℕ} (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z) :
    nonfoodMass x ≤ polymerMass x := by
  apply Finset.sum_le_sum
  intro z _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (hx z)

theorem collective_reduced_drift {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → ℝ) (cat : Reaction n → Molecule n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z)
    (hb : ∀ r, (1/500000000:ℝ) ≤ basal r ∧ basal r ≤ 4*(1/500000000))
    (ha : ∀ r z, 0 ≤ cat r z ∧ cat r z ≤ 16)
    (hfood : ∀ z, molLength z ≤ 2 → c z = ∅)
    (hL : polymerMass x ≤ 11) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hp : molLength (reactionProduct r) = 4)
    (hsel : r ∈ c (reactionProduct r)) (hcat : 4 ≤ cat r (reactionProduct r)) :
    1-1358*x (reactionLeft r) ≤ collectiveVectorField c basal cat x (reactionLeft r) ∧
    1-1358*x (reactionRight r) ≤ collectiveVectorField c basal cat x (reactionRight r) ∧
    (1/500000000:ℝ)*x (reactionLeft r)*x (reactionRight r)-1476*x (reactionProduct r) ≤
      collectiveVectorField c basal cat x (reactionProduct r) := by
  let speed := collectivePairSpeed c basal cat x
  have hs0 : ∀ r, 0 ≤ speed r := collective_pair_speed_nonneg c basal cat x hx
    (fun r => (by norm_num : (0:ℝ) ≤ 1/500000000).trans (hb r).1) (fun r z => (ha r z).1)
  have hs : ∀ r, speed r ≤ 59 := by
    intro q
    have hh := collective_pair_speed_bound c basal cat x hx (1/500000000)
      (fun r => (hb r).2) (fun r z => (ha r z).2) hfood q
    have hm := (nonfoodMass_le_mass x hx).trans hL
    linarith
  have hu := collective_food_drift speed x hs0 hx 59 (by norm_num) hs hL (reactionLeft r) hl
  have hw := collective_food_drift speed x hs0 hx 59 (by norm_num) hs hL (reactionRight r) hr
  have ht := collective_pair_speed_target c basal cat x hx (fun r z => (ha r z).1)
    (1/500000000) r (hb r).1 hcat hsel
  have hz := collective_product_drift speed x hs0 hx 59 (by norm_num) hs hL r hp (1/500000000) ht
  have hn : 0 ≤ 4*x (reactionLeft r)*x (reactionRight r)*x (reactionProduct r) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hx _)) (hx _)) (hx _)
  change 1-1358*x (reactionLeft r) ≤ collectiveDrift speed x (reactionLeft r) ∧
    1-1358*x (reactionRight r) ≤ collectiveDrift speed x (reactionRight r) ∧
    (1/500000000:ℝ)*x (reactionLeft r)*x (reactionRight r)-1476*x (reactionProduct r) ≤
      collectiveDrift speed x (reactionProduct r)
  exact ⟨by linarith only [hu], by linarith only [hw], by linarith only [hz,hn]⟩

theorem collective_product_cap {n : ℕ} (x : Molecule n → ℝ) (hx : ∀ z, 0 ≤ x z)
    (hL : polymerMass x ≤ 11) (z : Molecule n) (hz : molLength z = 4) : x z ≤ 11/4 := by
  have h : (molLength z : ℝ)*x z ≤ polymerMass x :=
    Finset.single_le_sum (fun y _ => mul_nonneg (Nat.cast_nonneg _) (hx y)) (Finset.mem_univ z)
  have hlen : (molLength z : ℝ) = 4 := by exact_mod_cast hz
  rw [hlen] at h
  linarith

end
end RandomViability
