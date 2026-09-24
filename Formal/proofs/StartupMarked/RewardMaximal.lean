import proofs.StartupMarked.RewardClock

namespace StartupMarked
open Classical RandomViability MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem gamma_reward_crossing_tail (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (θ Γ T : ℝ) (hΓ : 0 ≤ Γ) (hT : 0 ≤ T)
    (hgen : ∀ X,(countMass X : ℝ) ≤ 11*V →
      (∑ ch,unboundedPhysicalRate c V 1 basal cat X ch*(Real.exp (θ*reward X ch)-1)) ≤
        gammaRewardTilt c V basal cat reward θ Γ X)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (δ : ℝ) (K : ℕ) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | signedMarkedRewardFluctuationBy c V basal cat reward T stop θ δ K z} ≤
      ENNReal.ofReal (Real.exp (-δ+θ^2*Γ*T)) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  let κ := jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
    (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  let m := gammaRewardMultiplier c V basal cat reward θ Γ T stop
  let L := δ-θ^2*Γ*T
  let a := ENNReal.ofReal (Real.exp L)
  let B := ENNReal.ofReal (Real.exp (-L))
  let W : Set (ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :=
    {z | ∀ i,0 ≤ (z (i+1)).2.2}
  have hw : ∀ᵐ z ∂μ,z ∈ W := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hc := predictable_product_crossing_bound μ κ
    (fun k => physicalTrajectoryLaw_transition (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N k)
    m (gammaRewardMultiplier_measurable c V basal cat reward θ Γ T stop hstop)
    (gamma_reward_clock_mean hn c V hV basal cat reward θ Γ T hgen stop) a K
  have hsub : W ∩ {z | signedMarkedRewardFluctuationBy c V basal cat reward T stop θ δ K z} ⊆
      {z | ∃ j,j ≤ K ∧ a ≤ trajectoryProduct m j z} := by
    intro z hz
    obtain ⟨j,hj,hA⟩ := hz.2
    refine ⟨j,hj,?_⟩
    dsimp only [m,a]
    rw [gamma_reward_product_exp]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have ht := censored_nonfood_time_bound V T hT stop z hz.1 j
    exact sub_le_sub hA
      (mul_le_mul_of_nonneg_left ht (by positivity))
  have heq : μ (W ∩ {z | signedMarkedRewardFluctuationBy c V basal cat reward T stop θ δ K z}) =
      μ {z | signedMarkedRewardFluctuationBy c V basal cat reward T stop θ δ K z} :=
    Measure.measure_inter_eq_of_ae hw
  have ht : a*μ {z | signedMarkedRewardFluctuationBy c V basal cat reward T stop θ δ K z} ≤ 1 := by
    rw [← heq]
    exact (mul_le_mul_right (measure_mono hsub) a).trans hc
  have hinv : B*a = 1 := by
    dsimp [B,a]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,neg_add_cancel,
      Real.exp_zero,ENNReal.ofReal_one]
  have hb : μ {z | signedMarkedRewardFluctuationBy c V basal cat reward T stop θ δ K z} ≤ B := by
    calc
      _ = B*(a*μ {z | signedMarkedRewardFluctuationBy c V basal cat reward T stop θ δ K z}) := by
        rw [← mul_assoc,hinv,one_mul]
      _ ≤ B*1 := mul_le_mul_right ht B
      _ = _ := mul_one _
  have he : -L = -δ+θ^2*Γ*T := by dsimp [L]; ring
  simpa only [B,he] using hb

theorem gamma_reward_any_index_tail (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (θ Γ T : ℝ) (hΓ : 0 ≤ Γ) (hT : 0 ≤ T)
    (hgen : ∀ X,(countMass X : ℝ) ≤ 11*V →
      (∑ ch,unboundedPhysicalRate c V 1 basal cat X ch*(Real.exp (θ*reward X ch)-1)) ≤
        gammaRewardTilt c V basal cat reward θ Γ X)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (δ : ℝ) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      (⋃ K,{z | signedMarkedRewardFluctuationBy c V basal cat reward T stop θ δ K z}) ≤
      ENNReal.ofReal (Real.exp (-δ+θ^2*Γ*T)) := by
  have hm : Monotone (fun K => {z | signedMarkedRewardFluctuationBy c V basal cat reward T stop θ δ K z}) := by
    intro K J hK z hz
    obtain ⟨j,hj,hA⟩ := hz
    exact ⟨j,hj.trans hK,hA⟩
  rw [hm.measure_iUnion]
  exact iSup_le (fun K => gamma_reward_crossing_tail hn c V hV basal cat N
    reward θ Γ T hΓ hT hgen stop hstop δ K)

theorem gamma_reward_two_sided_tail (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (Γ T δ : ℝ) (hΓ : 0 ≤ Γ) (hT : 0 ≤ T)
    (hgen : ∀ θ : ℝ,|θ| ≤ 1 → ∀ X,(countMass X : ℝ) ≤ 11*V →
      (∑ ch,unboundedPhysicalRate c V 1 basal cat X ch*(Real.exp (θ*reward X ch)-1)) ≤
        gammaRewardTilt c V basal cat reward θ Γ X)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) :
    physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N
      {z | ∃ K,δ ≤ |censoredMarkedRewardPrefix c V basal cat reward T stop z K|} ≤
      2*ENNReal.ofReal (Real.exp (-δ+Γ*T)) := by
  let μ := physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N
  let E := fun t : ℝ => ⋃ K,{z | signedMarkedRewardFluctuationBy c V basal cat reward T stop t δ K z}
  let B := ENNReal.ofReal (Real.exp (-δ+Γ*T))
  have hp : μ (E 1) ≤ B := by
    simpa only [one_pow,one_mul] using gamma_reward_any_index_tail hn c V hV basal cat N
      reward 1 Γ T hΓ hT (hgen 1 (by norm_num)) stop hstop δ
  have hm : μ (E (-1)) ≤ B := by
    simpa only [neg_one_sq,one_mul] using gamma_reward_any_index_tail hn c V hV basal cat N
      reward (-1) Γ T hΓ hT (hgen (-1) (by norm_num)) stop hstop δ
  have hsub : {z | ∃ K,δ ≤ |censoredMarkedRewardPrefix c V basal cat reward T stop z K|} ⊆
      E 1 ∪ E (-1) := by
    intro z hz
    obtain ⟨K,hK⟩ := hz
    rcases le_abs.mp hK with hp|hm
    · apply Or.inl
      apply Set.mem_iUnion.mpr
      exact ⟨K,K,le_rfl,by simpa only [one_mul] using hp⟩
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      exact ⟨K,K,le_rfl,by simpa only [neg_one_mul] using hm⟩
  calc
    _ ≤ μ (E 1 ∪ E (-1)) := measure_mono hsub
    _ ≤ μ (E 1)+μ (E (-1)) := measure_union_le _ _
    _ ≤ B+B := add_le_add hp hm
    _ = _ := (two_mul B).symm

end
end StartupMarked
