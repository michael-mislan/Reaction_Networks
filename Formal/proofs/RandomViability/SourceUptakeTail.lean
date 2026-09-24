import proofs.RandomViability.BoundedPathTail

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

def sourceAverage (a : ℝ) (n : ℕ) (f : SourceMoleculeFibreConfig n → ℝ) : ℝ :=
  ∑ c, sourcePowerLawConfigWeight a n c * f c

theorem sourceAverage_le_bad_add (a : ℝ) (n : ℕ) (ha : 1 < a) (hn : 4 ≤ n)
    (E : SourceMoleculeFibreConfig n → Prop) (f : SourceMoleculeFibreConfig n → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hprob : ∀ c, f c ≤ 1) (hgood : ∀ c, ¬ E c → f c ≤ δ) :
    sourceAverage a n f ≤ eventMass a n E + δ := by
  calc
    _ ≤ ∑ c, ((if E c then sourcePowerLawConfigWeight a n c else 0) +
        sourcePowerLawConfigWeight a n c * δ) := by
      apply Finset.sum_le_sum
      intro c _
      have hw := sourcePowerLawConfigWeight_nonneg a n ha c
      by_cases hc : E c
      · rw [if_pos hc]
        have hh := mul_le_mul_of_nonneg_left (hprob c) hw
        have hd := mul_nonneg hw hδ
        linarith
      · rw [if_neg hc, zero_add]
        exact mul_le_mul_of_nonneg_left (hgood c hc) hw
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_sourcePowerLawConfigWeight_eq_one a n ha hn, one_mul]
      rfl

theorem source_bounded_uptake_tail_bound {n B k : ℕ} (hn : 4 ≤ n) (hk : 0 < k)
    (a : ℝ) (ha : 1 < a) (V D : NNReal) (hV : 1 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (κ : ℝ) (hκ : 0 ≤ κ) (hrate : ∀ r z, (catalytic r z : ℝ) ≤ κ)
    (q : SourceMoleculeFibreConfig n → NNReal) (hq : ∀ c, 0 < (q c : ℝ))
    (hqD : ∀ c, (D : ℝ) ≤ 2*q c)
    (hbound : ∀ c (X : BoundedCounts n B), (boundedPhysicalCountModel c V D basal catalytic).total X ≤ q c)
    (N : BoundedCounts n B) (hinit : ((boundedMass N : ℝ)/V)^3 ≤ 38000)
    (t : NNReal) (ht : 0 < (t : ℝ)) (j : ℝ) (hj : 0 < j) :
    sourceAverage a n (fun c => boundedUptakeTail c V D basal catalytic (q c) (hq c) (hbound c) N t (j*V*t)) ≤
      (Fintype.card (Molecule k) * Fintype.card (Reaction (k+2)) : ℕ) *
        (windowZipfMean a (sourceReactionCount n) / sourceReactionCount n) + 152000*κ/((k : ℝ)*j) := by
  have hp : ∀ c, boundedUptakeTail c V D basal catalytic (q c) (hq c) (hbound c) N t (j*V*t) ≤ 1 := by
    intro c
    exact ((labeledUniformize (boundedPhysicalCountModel c V D basal catalytic) (q c) (hq c)
      (hbound c)).poissonPathTail_bounds _ (q c*t) N (j*V*t)).2
  have hg : ∀ c, ¬ ShortIncidence k c →
      boundedUptakeTail c V D basal catalytic (q c) (hq c) (hbound c) N t (j*V*t) ≤ 152000*κ/((k : ℝ)*j) := by
    intro c hc
    exact bounded_uptake_tail_bound (by omega) hk c hc V D hV basal catalytic κ hκ hrate
      (q c) (hq c) (hqD c) (hbound c) N hinit t ht j hj
  have hh := sourceAverage_le_bad_add a n ha hn (ShortIncidence k) _
    (152000*κ/((k : ℝ)*j)) (by positivity) hp hg
  exact hh.trans (add_le_add (shortIncidence_mass_le a n k ha hn) (le_refl _))

end
end RandomViability

