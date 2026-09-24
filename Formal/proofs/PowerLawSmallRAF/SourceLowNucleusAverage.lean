import proofs.PowerLawSmallRAF.SourceNucleusPositiveProbability
import proofs.PowerLawSmallRAF.SourceUnionParameterProbability

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem sourceLowUnionFloor_gt_half : (1/2 : ℝ) < 1-Real.exp (-(4/5 : ℝ)) := by
  have hx : (19/15 : ℝ) ≤ Real.exp (4/15 : ℝ) := by
    linarith [Real.add_one_le_exp (4/15 : ℝ)]
  have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 19/15) hx 3
  have he : Real.exp (4/5 : ℝ) = Real.exp (4/15 : ℝ)^3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [← he] at hc
  have h2 : (2 : ℝ) < Real.exp (4/5 : ℝ) := by norm_num at hc; linarith
  have hi : Real.exp (-(4/5 : ℝ)) < 1/2 := by
    rw [Real.exp_neg,← one_div]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    linarith
  linarith

def sourceNucleusProbabilityFloor : ℝ :=
  Real.exp (-4/(2*(1-Real.exp (-(4/5 : ℝ)))-1))

theorem sourceNucleusProbabilityFloor_pos : 0 < sourceNucleusProbabilityFloor := Real.exp_pos _

def sourceLowNucleusMass (n L : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    sourceNucleusMarkMass (sourceLowUnionParameter n d) n L

theorem sourceNucleusMarkMass_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n L : Nat) :
    0 ≤ sourceNucleusMarkMass p n L := by
  unfold sourceNucleusMarkMass
  apply Finset.sum_nonneg
  intro H _
  exact mul_nonneg (bernoulliSubsetRowWeight_nonneg hp hp1 H) (by split_ifs <;> norm_num)

/-- Average over the actual Zipf degree law; no unconditional iid assertion
is made. Bad low-intensity degree configurations are discarded explicitly. -/
theorem sourceLowNucleusMass_lower (n L : Nat) (hn : 4 ≤ n) (hLn : L ≤ n) :
    sourceNucleusProbabilityFloor*(1-sourceLowUnionFailureMass n) ≤ sourceLowNucleusMass n L := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  have hp (d : SourceDegreeConfig n) :
      sourceNucleusProbabilityFloor*(1-(if sourceLowUnionParameter n d <
        1-Real.exp (-(4/5 : ℝ)) then 1 else 0)) ≤
        sourceNucleusMarkMass (sourceLowUnionParameter n d) n L := by
    have hq := (sourceBandUnionParameter_bounds n hn d).1
    by_cases hb : sourceLowUnionParameter n d < 1-Real.exp (-(4/5 : ℝ))
    · simp only [if_pos hb,sub_self,mul_zero]
      exact sourceNucleusMarkMass_nonneg _ hq.1 hq.2 n L
    · simp only [if_neg hb,sub_zero,mul_one]
      exact (sourceNucleusMarkMass_uniform_lower _ _ sourceLowUnionFloor_gt_half
        (le_of_not_gt hb) hq.2 n L hLn).2
  have he : (∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
      (sourceNucleusProbabilityFloor*(1-(if sourceLowUnionParameter n d <
        1-Real.exp (-(4/5 : ℝ)) then 1 else 0)))) =
      sourceNucleusProbabilityFloor*(1-sourceLowUnionFailureMass n) := by
    calc
      _ = sourceNucleusProbabilityFloor *
          ((∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d) -
            ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
              (if sourceLowUnionParameter n d < 1-Real.exp (-(4/5 : ℝ)) then 1 else 0)) := by
        rw [← Finset.sum_sub_distrib,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = _ := by rw [sourceDegreeWeight_sum_eq_one _ _ ha hn]; rfl
  rw [← he]
  apply Finset.sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_left (hp d) (sourceDegreeWeight_nonneg _ _ ha d)

theorem sourceLowNucleusMass_eventually_lower (L : Nat → Nat)
    (hL : ∀ᶠ n in atTop, L n ≤ n) :
    ∀ᶠ n in atTop, sourceNucleusProbabilityFloor/2 ≤ sourceLowNucleusMass n (L n) := by
  have hb : ∀ᶠ n in atTop, sourceLowUnionFailureMass n < 1/2 :=
    sourceLowUnionFailureMass_tendsto_zero.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hb,hL,eventually_ge_atTop 4] with n hn hLn h4
  have hh := sourceLowNucleusMass_lower n (L n) h4 hLn
  have hc := sourceNucleusProbabilityFloor_pos
  nlinarith

end
end PowerLawSmallRAF
