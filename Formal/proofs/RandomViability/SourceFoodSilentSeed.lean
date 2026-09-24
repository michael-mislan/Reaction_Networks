import proofs.RandomViability.SourceProductiveLower
import proofs.RandomViability.MassNoiseProbability

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000

def sourceEmptyRowMass (a : ℝ) (n : ℕ) : ℝ :=
  subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) (∅ : Finset (Reaction n))

def sourceFoodSilentSeed {n : ℕ} (x : Molecule n) (r : Reaction n)
    (c : SourceMoleculeFibreConfig n) : Prop :=
  (∀ y ∈ binaryFood n 2,c y = ∅) ∧ r ∈ c x

/-- Exact probability of six empty food rows and one nonfood incidence. -/
theorem source_food_silent_seed_mass {n : ℕ} (hn : 4 ≤ n) (a : ℝ) (ha : 1 < a)
    (x : Molecule n) (hx : x ∉ binaryFood n 2) (r : Reaction n) :
    (∑ c : SourceMoleculeFibreConfig n,
      if sourceFoodSilentSeed x r c then sourcePowerLawConfigWeight a n c else 0) =
      sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 := by
  let w : Finset (Reaction n) → ℝ := subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n))
  let f := fun y (A : Finset (Reaction n)) =>
    if y ∈ binaryFood n 2 then (if A = ∅ then w A else 0)
    else if y = x then (if r ∈ A then w A else 0) else w A
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2^n := by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have hwsum : (∑ A : Finset (Reaction n),w A) = 1 := by
    dsimp [w]
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  have hhit : (∑ A : Finset (Reaction n),if r ∈ A then w A else 0) =
      powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 := source_oneFibre_incidence_mass_eq_gatewayHit a ha hn r
  have hpoint (c : SourceMoleculeFibreConfig n) :
      (if sourceFoodSilentSeed x r c then ∏ y,w (c y) else 0) = ∏ y,f y (c y) := by
    by_cases he : sourceFoodSilentSeed x r c
    · rw [if_pos he]
      apply Finset.prod_congr rfl
      intro y _
      by_cases hy : y ∈ binaryFood n 2
      · simp [f,hy,he.1 y hy]
      · by_cases hyx : y = x
        · subst y
          simp [f,hx,he.2]
        · simp [f,hy,hyx]
    · rw [if_neg he]
      symm
      by_cases hf : ∀ y ∈ binaryFood n 2,c y = ∅
      · have hh : r ∉ c x := fun hh => he ⟨hf,hh⟩
        apply Finset.prod_eq_zero (Finset.mem_univ x)
        simp [f,hx,hh]
      · push Not at hf
        obtain ⟨y,hy,hy'⟩ := hf
        apply Finset.prod_eq_zero (Finset.mem_univ y)
        simp [f,hy,hy'.ne_empty]
  change (∑ c : SourceMoleculeFibreConfig n,if sourceFoodSilentSeed x r c then ∏ y,w (c y) else 0) = _
  simp_rw [hpoint]
  rw [← Fintype.prod_sum]
  have hcoordinate (y : Molecule n) : (∑ A : Finset (Reaction n),f y A) =
      if y ∈ binaryFood n 2 then w ∅ else
        if y = x then powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 else 1 := by
    by_cases hy : y ∈ binaryFood n 2
    · simp [f,hy]
    · by_cases hyx : y = x
      · simpa only [f,if_neg hy,if_pos hyx] using hhit
      · simpa only [f,if_neg hy,if_neg hyx] using hwsum
  simp_rw [hcoordinate]
  have he (y : Molecule n) :
      (if y ∈ binaryFood n 2 then w ∅ else if y = x then powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 else 1) =
      (if y ∈ binaryFood n 2 then w ∅ else 1)*
        (if y = x then powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 else 1) := by
    by_cases hy : y ∈ binaryFood n 2
    · have hyx : y ≠ x := fun h => hx (h ▸ hy)
      simp [hy,hyx]
    · simp [hy]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,Finset.prod_ite_mem_eq,Finset.prod_ite_eq']
  have hfood : (binaryFood n 2).card = 6 := by simpa only [Fintype.card_coe] using six_food_coordinates (by omega : 2 ≤ n)
  simp only [Finset.prod_const,hfood,Finset.mem_univ,if_true]
  rfl

theorem sourceAverage_food_silent_seed_lower {n : ℕ} (hn : 4 ≤ n) (a : ℝ) (ha : 1 < a)
    (x : Molecule n) (hx : x ∉ binaryFood n 2) (r : Reaction n)
    (b : ℝ) (f : SourceMoleculeFibreConfig n → ℝ)
    (hf : ∀ c,0 ≤ f c) (hb : ∀ c,sourceFoodSilentSeed x r c → b ≤ f c) :
    (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*b ≤
      sourceAverage a n f := by
  rw [← source_food_silent_seed_mass hn a ha x hx r,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  have hw := sourcePowerLawConfigWeight_nonneg a n ha c
  by_cases hc : sourceFoodSilentSeed x r c
  · rw [if_pos hc]
    exact mul_le_mul_of_nonneg_left (hb c hc) hw
  · rw [if_neg hc,zero_mul]
    exact mul_nonneg hw (hf c)

end
end RandomViability
