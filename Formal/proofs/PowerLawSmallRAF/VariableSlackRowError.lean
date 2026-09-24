import proofs.PowerLawSmallRAF.SourceActiveRowError

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section

/-- Source degree averaging with an arbitrary nonnegative row slack.
Inactive rows contribute no overflow and are not charged a union penalty. -/
theorem sourceMixedRowOverflowMass_le_variable_slack (a : ℝ) (n L : Nat)
    (ha : 1 < a) (hn : 4 ≤ n) (ε : ℝ) (hε : 0 ≤ ε)
    (p : SourceDegreeConfig n → Molecule n → ℝ)
    (hp : ∀ d x, 0 ≤ p d x) (hp1 : ∀ d x, p d x ≤ 1)
    (hsmall : ∀ d x, (d x).val < L → p d x = 0)
    (hmean : ∀ d x, (Fintype.card (Reaction n) : ℝ)*p d x ≤ (1-ε)*(d x : ℝ)) :
    sourceMixedRowOverflowMass a n p ≤
      (sourceMoleculeCount n : ℝ)*Real.exp (-ε^2*(L : ℝ)/4) := by
  have hrow (d : SourceDegreeConfig n) (x : Molecule n) :
      bernoulliRowOverflowMass (J := Reaction n) (p d x) (d x) ≤ Real.exp (-ε^2*(L : ℝ)/4) := by
    by_cases hd : (d x).val < L
    · rw [hsmall d x hd,bernoulliRowOverflowMass_zero]
      positivity
    · apply (bernoulliRowOverflowMass_le_exp_slack (J := Reaction n) (hp d x) (hp1 d x)
        (d x) ε hε (hmean d x)).trans
      apply Real.exp_le_exp.mpr
      have hLd : (L : ℝ) ≤ (d x : ℝ) := by exact_mod_cast (Nat.le_of_not_gt hd)
      nlinarith [mul_le_mul_of_nonneg_left hLd (sq_nonneg ε)]
  have hsum (d : SourceDegreeConfig n) :
      (∑ x, bernoulliRowOverflowMass (J := Reaction n) (p d x) (d x)) ≤
        (sourceMoleculeCount n : ℝ)*Real.exp (-ε^2*(L : ℝ)/4) := by
    calc
      _ ≤ ∑ _x : Molecule n, Real.exp (-ε^2*(L : ℝ)/4) := Finset.sum_le_sum (fun x _ => hrow d x)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_binaryMolecule_eq_sourceMoleculeCount]
  calc
    _ ≤ ∑ d : SourceDegreeConfig n, sourceDegreeWeight a n d *
        ((sourceMoleculeCount n : ℝ)*Real.exp (-ε^2*(L : ℝ)/4)) :=
      Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left (hsum d) (sourceDegreeWeight_nonneg a n ha d))
    _ = _ := by rw [← Finset.sum_mul,sourceDegreeWeight_sum_eq_one a n ha hn,one_mul]

end
end PowerLawSmallRAF
