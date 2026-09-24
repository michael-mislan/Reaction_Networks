import proofs.CoreCouplingCAC.Creation

namespace CoreCouplingCAC

noncomputable def lowerState (l r : ℝ) : State :=
  ⟨l*(60/(r+2))+(20004*l^2-159984*r)/20001,
   60/(r+2),l,(160000*l+20000*l^2)/20001⟩
noncomputable def upperState (l r : ℝ) : State :=
  ⟨r*(60/(l+2))+(20004*r^2-159984*l)/20001,
   60/(l+2),r,(160000*r+20000*r^2)/20001⟩

def InBox (x lo hi : State) : Prop :=
  lo.A ≤ x.A ∧ x.A ≤ hi.A ∧ lo.B ≤ x.B ∧ x.B ≤ hi.B ∧
  lo.z ≤ x.z ∧ x.z ≤ hi.z ∧ lo.H ≤ x.H ∧ x.H ≤ hi.H

theorem lift_interval_enclosure (l r z : ℝ) (hl : 0 < l)
    (hlz : l ≤ z) (hzr : z ≤ r) :
    InBox (lift witnessRates z) (lowerState l r) (upperState l r) := by
  have hz : 0 < z := lt_of_lt_of_le hl hlz
  have hr : 0 < r := lt_of_lt_of_le hz hzr
  have hsq₁ : l^2 ≤ z^2 := by nlinarith [sq_nonneg (z-l)]
  have hsq₂ : z^2 ≤ r^2 := by nlinarith [sq_nonneg (r-z)]
  have hB₁ : 60/(r+2) ≤ reducedB witnessRates z := by
    dsimp [reducedB,witnessRates]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    linarith
  have hB₂ : reducedB witnessRates z ≤ 60/(l+2) := by
    dsimp [reducedB,witnessRates]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    linarith
  have hK₁ : (20004*l^2-159984*r)/20001 ≤ reducedK witnessRates z := by
    rw [witness_K]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<20001)).2
    nlinarith
  have hK₂ : reducedK witnessRates z ≤ (20004*r^2-159984*l)/20001 := by
    rw [witness_K]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<20001)).2
    nlinarith
  have hA₁ := mul_le_mul hlz hB₁ (by positivity : (0:ℝ) ≤ 60/(r+2)) hz.le
  have hA₂ := mul_le_mul hzr hB₂ (by dsimp [reducedB,witnessRates]; positivity) hr.le
  have hH : reducedH witnessRates z = (160000*z+20000*z^2)/20001 := by
    norm_num [reducedH,witnessRates]
    ring
  unfold InBox
  dsimp [lift,lowerState,upperState]
  refine ⟨?_,?_,hB₁,hB₂,hlz,hzr,?_,?_⟩
  · dsimp [reducedA]
    linarith
  · dsimp [reducedA]
    linarith
  · rw [hH]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<20001)).2
    nlinarith
  · rw [hH]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<20001)).2
    nlinarith

theorem narrow_outer_roots :
    (∃ z ∈ Set.Icc (995794/1000000:ℝ) (995795/1000000), residual witnessRates z = 0) ∧
    (∃ z ∈ Set.Icc (2976367/1000000:ℝ) (2976368/1000000), residual witnessRates z = 0) := by
  constructor
  · apply intermediate_value_Icc (by norm_num)
      (residual_continuousOn _ _ (by norm_num))
    constructor <;> norm_num [residual,reducedA,reducedB,reducedK,witnessRates]
  · apply intermediate_value_Icc (by norm_num)
      (residual_continuousOn _ _ (by norm_num))
    constructor <;> norm_num [residual,reducedA,reducedB,reducedK,witnessRates]

end CoreCouplingCAC
