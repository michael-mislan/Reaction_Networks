import proofs.StartupMarked.MissionAE
import proofs.StartupMarked.ControlProbability
import proofs.StartupMarked.SourceNoise
import proofs.RepeatedFunction.MissionMeasurable

namespace StartupMarked
open Classical RandomViability StartupCount MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 80000
variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]
theorem startup_mission_failure (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (hVn : 10000000000000*(n : ℝ) ≤ V)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcatCap : ∀ r q,(cat r q : ℝ) ≤ 16)
    (hfood : ∀ q,molLength q ≤ 2 → c q = ∅) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hbas : (1/500000000 : ℝ) ≤ basal r)
    (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (N : Molecule n → ℕ)
    (hinitM : (countMass N : ℝ)/V ≤ 10)
    (hinitL : (N (reactionLeft r) : ℝ)/V = 1)
    (hinitR : (N (reactionRight r) : ℝ)/V = 1)
    : physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 (by linarith) (by norm_num) basal cat N
        {z | ¬twoWindowMission V z} < ENNReal.ofReal (11/10000 : ℝ) := by
  have hv : 0 < (V : ℝ) := by linarith
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hv (by norm_num) basal cat N
  let EC := {z | ¬retainedControls c V basal cat r z}
  let EF := lowDuring (β := PhysicalCountChannel n) (countGuard V r) (fun X => X (reactionProduct r)) (stockThreshold V) 1 199
  let EM := {z | ¬markedRewardNoiseBound c V basal cat (cutoffReward V r stockCutoff) 200 15 z}
  have hcontrol : μ EC < ENNReal.ofReal (1/1000 : ℝ) := retained_controls_uniform hn c V hV hVn
    basal cat N r (fun rr => (hb rr).trans (by norm_num)) hcatCap
  have hfloor : μ EF < ENNReal.ofReal (1/1000000 : ℝ) := source_count_floor_uniform (by omega)
    c V hV basal cat r hb hcatCap hfood hlen huw huz hwz hbas N
  have hmarked : μ EM < ENNReal.ofReal (99/1000000 : ℝ) := by
    have hh := source_cutoff_interval_tail (by omega : 2 ≤ n) c V hV basal cat N r hb hcatCap hfood
      hl hr hlen huw huz hwz
    have hsub : EM ⊆ {z | ∃ k s,0 ≤ s ∧ s ≤ min (z (k+1)).2.2
        (200-prefixElapsed k (Preorder.frestrictLe k z)) ∧
        15 ≤ |markedRewardWithinInterval c V basal cat (cutoffReward V r stockCutoff)
          200 (massExitStop V) z k s|} := by
      intro z hz
      change ¬markedRewardNoiseBound c V basal cat (cutoffReward V r stockCutoff) 200 15 z at hz
      simp only [markedRewardNoiseBound] at hz
      push Not at hz
      obtain ⟨k,s,hs,hsh,hbad⟩ := hz
      exact ⟨k,s,hs,hsh,hbad.le⟩
    apply ((measure_mono hsub).trans hh).trans_lt
    have he : 2*ENNReal.ofReal (Real.exp (-10)) = ENNReal.ofReal (2*Real.exp (-10)) := by
      rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_ofNat]
    rw [he]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr marked_noise_sharp_scalar
  have hae := startup_two_window_ae (by omega : 2 ≤ n) c V hV basal cat hb hcatCap hfood r
    hl hr hlen huw huz hwz hsel hcat N hinitM hinitL hinitR
  have hsub : ∀ᵐ z ∂μ,z ∈ {z | ¬twoWindowMission V z} → z ∈ (EC ∪ EF) ∪ EM := by
    filter_upwards [hae] with z hz
    intro hbad
    by_contra h
    have hcgood : retainedControls c V basal cat r z := by
      by_contra hc'
      exact h (Or.inl (Or.inl hc'))
    have hfgood : z ∉ EF := fun hf => h (Or.inl (Or.inr hf))
    have hmgood : markedRewardNoiseBound c V basal cat (cutoffReward V r stockCutoff) 200 15 z := by
      by_contra hm
      exact h (Or.inr hm)
    exact hbad (hz hcgood.1 hcgood.2.1 hcgood.2.2.1 hfgood hmgood hcgood.2.2.2.1 hcgood.2.2.2.2)
  calc
    _ ≤ μ ((EC ∪ EF) ∪ EM) := measure_mono_ae hsub
    _ ≤ (μ EC+μ EF)+μ EM := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ < (ENNReal.ofReal (1/1000 : ℝ)+ENNReal.ofReal (1/1000000 : ℝ))+ENNReal.ofReal (99/1000000 : ℝ) :=
      ENNReal.add_lt_add (ENNReal.add_lt_add hcontrol hfloor) hmarked
    _ = _ := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      congr 1
      norm_num

end
end StartupMarked


