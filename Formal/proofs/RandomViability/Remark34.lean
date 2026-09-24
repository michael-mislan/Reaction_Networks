import proofs.RandomViability.SingletonConditionalConclusion
import proofs.RandomViability.ProductiveSingletonRAF

set_option Elab.async false
namespace RandomViability
open Classical Filter Topology MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 80000

theorem no_singleton_raf_implies_no_productive_singleton {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (h : ¬hasSingletonRAF c) : noProductiveSingleton c := by
  intro z r hsel hp
  exact h ⟨r,productive_incidence_singleton_isRAF c r z hp hsel⟩

theorem averaged_output_mono {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (a : ℝ) (ha : 1 < a) (A B : SourceMoleculeFibreConfig n → Prop) (hAB : ∀ c,A c → B c) :
    averagedOutputProbability hn V hV a A ≤ averagedOutputProbability hn V hV a B := by
  unfold averagedOutputProbability uniformFiniteAverage
  simp only [if_true]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro u _
  apply sourceAverage_mono a ha
  intro c
  by_cases hA : A c
  · rw [if_pos hA,if_pos (hAB c hA)]
  · rw [if_neg hA]
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl

/-- Every singleton RAF has globally minimum nonempty RAF cardinality. -/
theorem singleton_raf_minimum_card {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (h : hasSingletonRAF c) :
    ∃ Q : Finset (Reaction n),IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig c) Q ∧
      Q.card = 1 ∧ ∀ P : Finset (Reaction n),
        IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig c) P → Q.card ≤ P.card := by
  obtain ⟨r,hr⟩ := h
  refine ⟨{r},hr,Finset.card_singleton _,?_⟩
  intro P hP
  rw [Finset.card_singleton]
  exact Finset.one_le_card.mpr hP.1

/-- Exact conditional form of Remark 3.4. Among productive environments that
have a RAF, the probability that the minimum RAF cardinality exceeds one tends
to zero. The numerator explicitly includes the RAF-existence condition. -/
theorem remark34_no_singleton_given_productive_raf_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => outputJointProbability volume hvolume
      (fun _ c => anySourceRAF c ∧ ¬hasSingletonRAF c) n/
      outputJointProbability volume hvolume (fun _ => anySourceRAF) n) atTop (𝓝 0) := by
  obtain ⟨L,U,hL,_,hbound⟩ := output_joint_probability_theta volume hvolume (fun _ => anySourceRAF)
    (fun n hn c hs => ⟨{productiveReaction hn},productive_singleton_isRAF hn c hs.2⟩)
  have hu := (output_without_productive_singleton_relative_tendsto_zero volume hvolume).div_const L
  simp only [zero_div] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [hbound,source_incidence_ge_exp_eventually,eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hb hp hn ha
    have hden : 0 < outputJointProbability volume hvolume (fun _ => anySourceRAF) n :=
      (mul_pos hL hp.1).trans_le hb.1
    apply div_nonneg _ hden.le
    unfold outputJointProbability
    rw [dif_pos hn]
    exact averaged_output_nonneg hn _ _ _ ha _
  · filter_upwards [hbound,source_incidence_ge_exp_eventually,eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hb hp hn ha
    have hnum : 0 ≤ outputJointProbability volume hvolume (fun _ => noProductiveSingleton) n := by
      unfold outputJointProbability
      simp only [dif_pos hn]
      exact averaged_output_nonneg hn _ _ _ ha _
    have hden : 0 < outputJointProbability volume hvolume (fun _ => anySourceRAF) n :=
      (mul_pos hL hp.1).trans_le hb.1
    have hm : outputJointProbability volume hvolume (fun _ c => anySourceRAF c ∧ ¬hasSingletonRAF c) n ≤
        outputJointProbability volume hvolume (fun _ => noProductiveSingleton) n := by
      unfold outputJointProbability
      simp only [dif_pos hn]
      apply averaged_output_mono hn _ _ _ ha
      exact fun c hc => no_singleton_raf_implies_no_productive_singleton c hc.2
    have hh := (div_le_div_of_nonneg_right hm hden.le).trans
      (div_le_div_of_nonneg_left hnum (mul_pos hL hp.1) hb.1)
    convert hh using 1
    ring

end
end RandomViability
