import proofs.PowerLawSmallRAF.SourceDegreeCoupling

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 100000

def sourceDegreeWeight (a : ℝ) (n : Nat) (d : SourceDegreeConfig n) : ℝ :=
  ∏ x, cappedZipfDegreeMass a (sourceReactionCount n) (d x)

theorem sourceDegreeWeight_nonneg (a : ℝ) (n : Nat) (ha : 1 < a) (d : SourceDegreeConfig n) :
    0 ≤ sourceDegreeWeight a n d := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  exact Finset.prod_nonneg (fun x _ => cappedZipfDegreeMass_nonneg a _ (d x) hzpos)

theorem sourceDegreeWeight_sum_eq_one (a : ℝ) (n : Nat) (ha : 1 < a) (hn : 4 ≤ n) :
    (∑ d : SourceDegreeConfig n, sourceDegreeWeight a n d) = 1 := by
  have hcard := card_binaryReaction_eq_sourceReactionCount (by omega : 2 ≤ n)
  have hs : (∑ d : Fin (Fintype.card (Reaction n)+1),
      cappedZipfDegreeMass a (sourceReactionCount n) d) = 1 := by
    rw [Fin.sum_univ_eq_sum_range, hcard, Finset.sum_range_succ]
    have hz : cappedZipfDegreeMass a (sourceReactionCount n) (sourceReactionCount n) = 0 := by
      simp [cappedZipfDegreeMass]
    rw [hz, add_zero]
    exact cappedZipfDegreeMass_sum_eq_one a _ ha (by simp [sourceReactionCount])
  simp only [sourceDegreeWeight]
  rw [← Fintype.prod_sum (fun (_ : Molecule n) (d : Fin (Fintype.card (Reaction n)+1)) =>
    cappedZipfDegreeMass a (sourceReactionCount n) d)]
  simp_rw [hs]
  simp

def sourceMixedRowOverflowMass (a : ℝ) (n : Nat)
    (p : SourceDegreeConfig n → Molecule n → ℝ) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight a n d *
    ∑ x, bernoulliRowOverflowMass (J := Reaction n) (p d x) (d x)

theorem sourceMixedRowOverflowMass_nonneg (a : ℝ) (n : Nat) (ha : 1 < a)
    (p : SourceDegreeConfig n → Molecule n → ℝ)
    (hp : ∀ d x, 0 ≤ p d x) (hp1 : ∀ d x, p d x ≤ 1) :
    0 ≤ sourceMixedRowOverflowMass a n p := by
  apply Finset.sum_nonneg
  intro d _
  apply mul_nonneg (sourceDegreeWeight_nonneg a n ha d)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro B _
  split_ifs
  · exact bernoulliSubsetRowWeight_nonneg (hp d x) (hp1 d x) B
  · exact le_rfl

/-- All inactive rows have exactly zero overflow. The minimum active degree
controls the sum without conditioning the auxiliary law on coupling success. -/
theorem sourceMixedRowOverflowMass_le (a : ℝ) (n L : Nat) (ha : 1 < a) (hn : 4 ≤ n)
    (p : SourceDegreeConfig n → Molecule n → ℝ)
    (hp : ∀ d x, 0 ≤ p d x) (hp1 : ∀ d x, p d x ≤ 1)
    (hsmall : ∀ d x, (d x).val < L → p d x = 0)
    (hmean : ∀ d x, (Fintype.card (Reaction n) : ℝ)*p d x ≤ (19/20 : ℝ)*(d x : ℝ)) :
    sourceMixedRowOverflowMass a n p ≤
      (sourceMoleculeCount n : ℝ)*Real.exp (-(L : ℝ)/1600) := by
  have hrow (d : SourceDegreeConfig n) (x : Molecule n) :
      bernoulliRowOverflowMass (J := Reaction n) (p d x) (d x) ≤ Real.exp (-(L : ℝ)/1600) := by
    by_cases hd : (d x).val < L
    · rw [hsmall d x hd, bernoulliRowOverflowMass_zero]
      positivity
    · have htail := bernoulliRowOverflowMass_le_exp_slack (J := Reaction n) (hp d x) (hp1 d x) (d x)
        (1/20 : ℝ) (by norm_num) (by
          simpa only [show (1 : ℝ)-1/20 = 19/20 by norm_num] using hmean d x)
      apply htail.trans
      apply Real.exp_le_exp.mpr
      have hLd : (L : ℝ) ≤ (d x : ℝ) := by exact_mod_cast (Nat.le_of_not_gt hd)
      nlinarith only [hLd]
  have hsum (d : SourceDegreeConfig n) :
      (∑ x, bernoulliRowOverflowMass (J := Reaction n) (p d x) (d x)) ≤
        (sourceMoleculeCount n : ℝ)*Real.exp (-(L : ℝ)/1600) := by
    calc
      _ ≤ ∑ _x : Molecule n, Real.exp (-(L : ℝ)/1600) := Finset.sum_le_sum (fun x _ => hrow d x)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_binaryMolecule_eq_sourceMoleculeCount]
  calc
    _ ≤ ∑ d : SourceDegreeConfig n, sourceDegreeWeight a n d *
        ((sourceMoleculeCount n : ℝ)*Real.exp (-(L : ℝ)/1600)) :=
      Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left (hsum d) (sourceDegreeWeight_nonneg a n ha d))
    _ = _ := by rw [← Finset.sum_mul, sourceDegreeWeight_sum_eq_one a n ha hn, one_mul]

end
end PowerLawSmallRAF
