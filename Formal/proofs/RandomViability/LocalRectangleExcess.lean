import proofs.RandomViability.LocalExcessInequality
import proofs.PowerLawSmallRAF.SourceSplitBlockTail

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 70000

def localRectangleCount {n : ℕ} (H : Finset (Molecule n)) (T : Finset (Reaction n))
    (c : SourceMoleculeFibreConfig n) : ℕ :=
  ∑ i ∈ H.product T,if i.2 ∈ c i.1 then 1 else 0

theorem local_rectangle_zero_iff {n : ℕ} (H : Finset (Molecule n)) (T : Finset (Reaction n))
    (c : SourceMoleculeFibreConfig n) :
    localRectangleCount H T c = 0 ↔ ∀ x : ↥H,Disjoint (c x) T := by
  simp only [localRectangleCount,Finset.sum_eq_zero_iff]
  constructor
  · intro hh x
    apply Finset.disjoint_left.mpr
    intro r hr hT
    have he := hh (x.val,r) (Finset.mem_product.mpr ⟨x.property,hT⟩)
    simp [hr] at he
  · intro hh i hi
    obtain ⟨hx,hr⟩ := Finset.mem_product.mp hi
    have hn : i.2 ∉ c i.1 := fun hc => Finset.disjoint_left.mp (hh ⟨i.1,hx⟩) hc hr
    simp [hn]

theorem local_rectangle_expectation_le {n : ℕ} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (T : Finset (Reaction n)) :
    (∑ c : SourceMoleculeFibreConfig n,sourcePowerLawConfigWeight a n c*(localRectangleCount H T c : ℝ)) ≤
      (H.card : ℝ)*(T.card : ℝ)*(windowZipfMean a (sourceReactionCount n)/sourceReactionCount n) := by
  have he (c : SourceMoleculeFibreConfig n) :
      sourcePowerLawConfigWeight a n c*(localRectangleCount H T c : ℝ) =
        ∑ i ∈ H.product T,if i.2 ∈ c i.1 then sourcePowerLawConfigWeight a n c else 0 := by
    simp only [localRectangleCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  simp_rw [he]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i ∈ H.product T,windowZipfMean a (sourceReactionCount n)/sourceReactionCount n := by
      apply Finset.sum_le_sum
      intro i _
      exact source_single_incidence_mass_le_mean_div a ha hn i.1 i.2
    _ = _ := by simp [Finset.card_product,Nat.cast_mul,mul_assoc]

theorem local_rectangle_excess_bound {n : ℕ} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (T : Finset (Reaction n)) :
    eventMass a n (fun c => 2 ≤ localRectangleCount H T c) ≤
      (H.card : ℝ)*(T.card : ℝ)*(windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)-
      (1-(powerLawMoleculeGatewayMiss a (sourceReactionCount n) T.card)^H.card) := by
  have hzero := source_jointMiss_mass_eq_pow a ha hn H T
  rw [powerLawCoverageMissProfile_eq] at hzero
  have hsplit : (∑ c : SourceMoleculeFibreConfig n,if 1 ≤ localRectangleCount H T c then sourcePowerLawConfigWeight a n c else 0) =
      1-(powerLawMoleculeGatewayMiss a (sourceReactionCount n) T.card)^H.card := by
    have hp : ∀ c : SourceMoleculeFibreConfig n,
        (if 1 ≤ localRectangleCount H T c then sourcePowerLawConfigWeight a n c else 0)+
        (if ∀ x : ↥H,Disjoint (c x) T then sourcePowerLawConfigWeight a n c else 0) = sourcePowerLawConfigWeight a n c := by
      intro c
      simp only [← local_rectangle_zero_iff]
      by_cases he : localRectangleCount H T c = 0
      · simp [he]
      · simp [he,show 1 ≤ localRectangleCount H T c by omega]
    have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun c _ => hp c)
    rw [Finset.sum_add_distrib,hzero,sum_sourcePowerLawConfigWeight_eq_one a n ha hn] at hs
    linarith only [hs]
  have hh := finite_weighted_excess_bound (sourcePowerLawConfigWeight a n)
    (sourcePowerLawConfigWeight_nonneg a n ha) (localRectangleCount H T)
  rw [hsplit] at hh
  have hevent : eventMass a n (fun c => 2 ≤ localRectangleCount H T c) =
      ∑ c : SourceMoleculeFibreConfig n,if 2 ≤ localRectangleCount H T c then sourcePowerLawConfigWeight a n c else 0 := by
    unfold eventMass
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : 2 ≤ localRectangleCount H T c <;> simp only [hc,if_true,if_false]
  rw [hevent]
  exact hh.trans (sub_le_sub_right (local_rectangle_expectation_le a ha hn H T) _)

theorem local_rectangle_quadratic_bound {n : ℕ} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (T : Finset (Reaction n)) (hT : 0 < T.card) :
    eventMass a n (fun c => 2 ≤ localRectangleCount H T c) ≤
      (H.card : ℝ)*((T.card : ℝ)/((sourceReactionCount n-T.card+1 : ℕ) : ℝ))^2*
        windowZipfSecondMoment a (sourceReactionCount n)+
      (H.card : ℝ)^2*((T.card : ℝ)*windowZipfMean a (sourceReactionCount n)/
        ((sourceReactionCount n-T.card+1 : ℕ) : ℝ))^2 := by
  have hR : 2 ≤ sourceReactionCount n := by simp [sourceReactionCount]
  have hTR : T.card ≤ sourceReactionCount n := by
    simpa only [card_binaryReaction_eq_sourceReactionCount (by omega : 2 ≤ n)] using Finset.card_le_univ T
  have hh := powerLawMoleculeGatewayHit_bounds a (sourceReactionCount n) T.card ha hR hT hTR
  have hrange := powerLawMoleculeGatewayHit_nonneg_le_one a (sourceReactionCount n) T.card ha hR
  have hunion := finite_union_excess_le_square (powerLawMoleculeGatewayHit a (sourceReactionCount n) T.card)
    hrange.1 hrange.2 H.card
  have hsq := pow_le_pow_left₀ hrange.1 hh.2 2
  have hz : (0 : ℝ) ≤ H.card := by positivity
  have hlo := mul_le_mul_of_nonneg_left hh.1 hz
  have hhi := mul_le_mul_of_nonneg_left hsq (sq_nonneg (H.card : ℝ))
  have hb := local_rectangle_excess_bound a ha hn H T
  have he : powerLawMoleculeGatewayMiss a (sourceReactionCount n) T.card =
      1-powerLawMoleculeGatewayHit a (sourceReactionCount n) T.card := by
    unfold powerLawMoleculeGatewayHit
    ring
  rw [he] at hb
  have halg : (H.card : ℝ)*((T.card : ℝ)*windowZipfMean a (sourceReactionCount n)/(sourceReactionCount n : ℝ)) =
      (H.card : ℝ)*(T.card : ℝ)*(windowZipfMean a (sourceReactionCount n)/(sourceReactionCount n : ℝ)) := by ring
  rw [mul_sub,halg] at hlo
  nlinarith only [hb,hlo,hunion,hhi]

end
end RandomViability
