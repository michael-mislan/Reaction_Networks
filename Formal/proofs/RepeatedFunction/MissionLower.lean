import proofs.RepeatedFunction.MissionScale
import proofs.RepeatedFunction.MissionMeasurable

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_two_window_success_lower (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcatCap : ∀ r q,(cat r q : ℝ) ≤ 16)
    (hfood : ∀ q,molLength q ≤ 2 → c q = ∅) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hbas : (1/500000000 : ℝ) ≤ basal r) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (N : Molecule n → ℕ)
    (hinitM : (countMass N : ℝ)/V ≤ 10)
    (hinitL : (N (reactionLeft r) : ℝ)/V = 1)
    (hinitR : (N (reactionRight r) : ℝ)/V = 1)
    (hinitP : (N (reactionProduct r) : ℝ)/V = 0)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) :
    1-24*Real.exp (-(twoWindowNoiseRate*(V : ℝ)/(n : ℝ))) ≤
      (physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
        {z | twoWindowMission V z}).toReal := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  have ht := physical_two_window_uniform_tail hn c V hV basal cat
    hb hcatCap hfood r hl hr hlen huw huz hwz hsel hbas hcat N hinitM hinitL hinitR hinitP hscale
  have hb' : (μ {z | ¬twoWindowMission V z}).toReal ≤
      24*Real.exp (-(twoWindowNoiseRate*(V : ℝ)/(n : ℝ))) := by
    have hh := ENNReal.toReal_mono (by finiteness) ht
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh
  have he := probReal_add_probReal_compl (μ := μ) (two_window_mission_measurable V)
  change (μ {z | twoWindowMission V z}).toReal+(μ {z | ¬twoWindowMission V z}).toReal = 1 at he
  change 1-24*Real.exp (-(twoWindowNoiseRate*(V : ℝ)/(n : ℝ))) ≤ (μ {z | twoWindowMission V z}).toReal
  linarith only [he,hb']


end
end RandomViability
