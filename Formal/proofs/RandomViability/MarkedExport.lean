import proofs.RandomViability.CollectiveNormalizedVariance

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

/-- Marked exported nonfood mass per volume. Only a dilution mark contributes. -/
def exportReward {n : ℕ} (V : NNReal) : PhysicalCountChannel n → ℝ
  | .inl (.inr q) => ((molLength q : ℝ)-foodMassWeight q)/V
  | _ => 0

theorem export_reward_bounds {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (ch : PhysicalCountChannel n) : 0 ≤ exportReward V ch ∧ exportReward V ch ≤ (n : ℝ)/V := by
  rcases ch with (f|q)|(b|c)
  · simp only [exportReward]
    exact ⟨le_rfl,by positivity⟩
  · have hl : (molLength q : ℝ) ≤ n := by exact_mod_cast (show molLength q ≤ n by simp [molLength])
    simp only [exportReward,foodMassWeight]
    split_ifs
    · simp only [sub_self,zero_div]
      exact ⟨le_rfl,by positivity⟩
    · simp only [sub_zero]
      exact ⟨by positivity,div_le_div_of_nonneg_right hl hV.le⟩
  · simp only [exportReward]
    exact ⟨le_rfl,by positivity⟩
  · simp only [exportReward]
    exact ⟨le_rfl,by positivity⟩

theorem export_reward_drift {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch * exportReward V ch) = countNonfoodMass N/V := by
  have he (q : Molecule n) : unboundedPhysicalRate c V 1 basal cat N (.inl (.inr q)) = (N q : ℝ) := by
    have hh := bounded_outflow_rate c V 1 hV basal cat (countsAtOwnMass N) q
    change unboundedPhysicalRate c V 1 basal cat N (.inl (.inr q)) = (1 : ℝ)*(N q : ℝ) at hh
    simpa only [one_mul] using hh
  simp only [Fintype.sum_sum_type,exportReward,mul_zero,Finset.sum_const_zero,
    zero_add,add_zero,he,countNonfoodMass,weightedCountMass,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem export_reward_quadratic {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch * (exportReward V ch)^2) ≤
      ((n : ℝ)/V)*(countNonfoodMass N/V) := by
  rw [← export_reward_drift c V hV basal cat N,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ch _
  have hb := export_reward_bounds V hV ch
  have hr := unboundedPhysicalRate_nonneg c V 1 basal cat N ch
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb.2 hb.1) hr]

end
end RandomViability
