import proofs.PowerLawSmallRAF.BernoulliUniformRowCoupling

namespace PowerLawSmallRAF

open scoped BigOperators

set_option maxHeartbeats 100000

noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

def bernoulliRowOverflowMass (p : ℝ) (d : Nat) : ℝ :=
  ∑ B : Finset J, if d < B.card then bernoulliSubsetRowWeight p B else 0

omit [DecidableEq J] in
theorem bernoulliSubsetRow_mgf (p t : ℝ) :
    (∑ B : Finset J, bernoulliSubsetRowWeight p B * Real.exp ((B.card : ℝ)*t)) =
      (1-p+p*Real.exp t)^Fintype.card J := by
  classical
  unfold bernoulliSubsetRowWeight
  simp_rw [Real.exp_nat_mul]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card
    (fun b => p^b * (1-p)^(Fintype.card J-b) * (Real.exp t)^b)]
  simp only [Finset.card_univ, nsmul_eq_mul]
  have h := add_pow (p*Real.exp t) (1-p) (Fintype.card J)
  simpa only [mul_pow, mul_comm, mul_left_comm, mul_assoc, add_comm] using h.symm

omit [DecidableEq J] in
theorem bernoulliSubsetRow_mgf_le_exp {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (∑ B : Finset J, bernoulliSubsetRowWeight p B * Real.exp ((B.card : ℝ)*t)) ≤
      Real.exp ((Fintype.card J : ℝ)*p*(Real.exp t-1)) := by
  rw [bernoulliSubsetRow_mgf]
  have hbase : 0 ≤ 1-p+p*Real.exp t :=
    add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hp (Real.exp_pos t).le)
  have hle : 1-p+p*Real.exp t ≤ Real.exp (p*(Real.exp t-1)) := by
    have h := Real.add_one_le_exp (p*(Real.exp t-1))
    nlinarith only [h]
  have hpow := pow_le_pow_left₀ hbase hle (Fintype.card J)
  rw [← Real.exp_nat_mul] at hpow
  simpa only [mul_assoc] using hpow

omit [DecidableEq J] in
theorem bernoulliRowOverflowMass_le_chernoff {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (d : Nat) (t : ℝ) (ht : 0 ≤ t) :
    bernoulliRowOverflowMass (J := J) p d ≤
      Real.exp (-(d : ℝ)*t+(Fintype.card J : ℝ)*p*(Real.exp t-1)) := by
  classical
  have hm : bernoulliRowOverflowMass (J := J) p d * Real.exp ((d : ℝ)*t) ≤
      ∑ B : Finset J, bernoulliSubsetRowWeight p B * Real.exp ((B.card : ℝ)*t) := by
    unfold bernoulliRowOverflowMass
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro B _
    split_ifs with hB
    · apply mul_le_mul_of_nonneg_left _ (bernoulliSubsetRowWeight_nonneg hp hp1 B)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ ht
      exact_mod_cast hB.le
    · simp only [zero_mul]
      exact mul_nonneg (bernoulliSubsetRowWeight_nonneg hp hp1 B) (Real.exp_pos _).le
  calc
    _ ≤ (∑ B : Finset J, bernoulliSubsetRowWeight p B * Real.exp ((B.card : ℝ)*t)) /
        Real.exp ((d : ℝ)*t) := (le_div_iff₀ (Real.exp_pos _)).mpr hm
    _ ≤ Real.exp ((Fintype.card J : ℝ)*p*(Real.exp t-1)) / Real.exp ((d : ℝ)*t) :=
      div_le_div_of_nonneg_right (bernoulliSubsetRow_mgf_le_exp (J := J) hp hp1 t) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

omit [DecidableEq J] in
/-- A multiplicative slack in the Bernoulli mean gives an exponentially
small containment defect, uniformly in catalogue size. -/
theorem bernoulliRowOverflowMass_le_exp_slack {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (d : Nat) (eps : ℝ) (heps : 0 ≤ eps)
    (hmean : (Fintype.card J : ℝ)*p ≤ (1-eps)*(d : ℝ)) :
    bernoulliRowOverflowMass (J := J) p d ≤ Real.exp (-eps^2*(d : ℝ)/4) := by
  let t := eps/2
  let y := Real.exp t-1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hy : t ≤ y := by
    have := Real.add_one_le_exp t
    dsimp [y]
    linarith
  have hy0 : 0 ≤ y := ht.trans hy
  have hraw := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (Real.exp_pos t).le
  have hcancel : Real.exp (-t)*Real.exp t = 1 := by rw [← Real.exp_add]; simp
  rw [hcancel] at hraw
  have hupper : (1-t)*y ≤ t := by dsimp [y]; nlinarith only [hraw]
  have hty := mul_le_mul_of_nonneg_left hy ht
  have hcoef : (1-eps)*y-t ≤ -eps^2/4 := by
    dsimp [t] at hupper hty ⊢
    nlinarith only [hupper, hty]
  have hmeanY := mul_le_mul_of_nonneg_right hmean hy0
  have hcoefD := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  apply (bernoulliRowOverflowMass_le_chernoff (J := J) hp hp1 d t ht).trans
  apply Real.exp_le_exp.mpr
  change -(d : ℝ)*t+(Fintype.card J : ℝ)*p*y ≤ -eps^2*(d : ℝ)/4
  nlinarith only [hmeanY, hcoefD]

theorem bernoulliUniformRowJointWeight_failure_le_exp_slack {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (d : Nat) (hd : d ≤ Fintype.card J)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hmean : (Fintype.card J : ℝ)*p ≤ (1-eps)*(d : ℝ)) :
    (∑ B : Finset J, ∑ T : Finset J,
      if ¬ B ⊆ T then bernoulliUniformRowJointWeight p d B T else 0) ≤
      Real.exp (-eps^2*(d : ℝ)/4) := by
  rw [bernoulliUniformRowJointWeight_containment_failure p d hd]
  exact bernoulliRowOverflowMass_le_exp_slack hp hp1 d eps heps hmean

end
end PowerLawSmallRAF
