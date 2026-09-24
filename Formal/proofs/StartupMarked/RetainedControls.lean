import proofs.RepeatedFunction.MissionProbability

namespace StartupMarked
open Classical RandomViability MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000

def retainedControls {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (r : Reaction n)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  massNoiseBound c V basal cat 200 (1/4) z ∧
  coordinateNoiseBound c V basal cat (reactionLeft r) 200 (1/100000) z ∧
  coordinateNoiseBound c V basal cat (reactionRight r) 200 (1/100000) z ∧
  markedRewardNoiseBound c V basal cat (fun _ => exportReward V) 200 (1/40) z ∧
  markedRewardNoiseBound c V basal cat (fun _ => grossFeedReward V) 200 1 z

def nonfoodExponent (n V d : ℝ) : ℝ := d^2*V/(4*n*(96011*200+d))
def coordinateExponent (V d : ℝ) : ℝ := d^2*V/(4*(96000*200+2*d))

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem retained_controls_failure (hn : 4 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 1) (hc : ∀ r q,(cat r q : ℝ) ≤ 16)
    (dN dM dF dE dB : ℝ) (hN : 0 < dN) (hM : 0 < dM) (hF : 0 < dF)
    (hE : 0 < dE) (hB : 0 < dB)
    (hmN : dN+(n : ℝ)/V ≤ 1/8) (hmM : dM+2/V ≤ 1/80)
    (hmF : dF+2/V ≤ 1/100000) (hmE : dE+(n : ℝ)/V ≤ 1/40)
    (hmB : dB+(n : ℝ)/V ≤ 1) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ¬retainedControls c V basal cat r z} ≤
      2*ENNReal.ofReal (Real.exp (-nonfoodExponent n V dN))+
      12*ENNReal.ofReal (Real.exp (-coordinateExponent V dM))+
      4*ENNReal.ofReal (Real.exp (-coordinateExponent V dF))+
      2*ENNReal.ofReal (Real.exp (-nonfoodExponent n V dE))+
      2*ENNReal.ofReal (Real.exp (-nonfoodExponent n V dB)) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  let EM := {z | ¬massNoiseBound c V basal cat 200 (1/4) z}
  let EL := {z | ¬coordinateNoiseBound c V basal cat (reactionLeft r) 200 (1/100000) z}
  let ER := {z | ¬coordinateNoiseBound c V basal cat (reactionRight r) 200 (1/100000) z}
  let EE := {z | ¬markedRewardNoiseBound c V basal cat (fun _ => exportReward V) 200 (1/40) z}
  let EB := {z | ¬markedRewardNoiseBound c V basal cat (fun _ => grossFeedReward V) 200 1 z}
  let BN := ENNReal.ofReal (Real.exp (-nonfoodExponent n V dN))
  let BM := ENNReal.ofReal (Real.exp (-coordinateExponent V dM))
  let BF := ENNReal.ofReal (Real.exp (-coordinateExponent V dF))
  let BE := ENNReal.ofReal (Real.exp (-nonfoodExponent n V dE))
  let BB := ENNReal.ofReal (Real.exp (-nonfoodExponent n V dB))
  have hm : μ EM ≤ 2*BN+12*BM := by
    have h := physical_mass_noise_failure hn c V hV basal cat N hb hc dN dM 200
      (1/8) (1/80) hN hM (by norm_num) hmN hmM
    rw [show (1/8 : ℝ)+10*(1/80) = 1/4 by norm_num] at h
    exact h
  have hl : μ EL ≤ 2*BF := physical_noise_bound_failure (by omega) c V hV basal cat N hb hc
    (reactionLeft r) dF 200 (1/100000) hF (by norm_num) hmF
  have hr : μ ER ≤ 2*BF := physical_noise_bound_failure (by omega) c V hV basal cat N hb hc
    (reactionRight r) dF 200 (1/100000) hF (by norm_num) hmF
  have he : μ EE ≤ 2*BE := physical_export_noise_failure hn c V hV basal cat N dE 200 (1/40) hE (by norm_num) hmE
  have hb' : μ EB ≤ 2*BB := physical_gross_feed_noise_failure hn c V hV basal cat N dB 200 1 hB (by norm_num) hmB
  have hsub : {z | ¬retainedControls c V basal cat r z} ⊆ ((EM ∪ EL) ∪ ER) ∪ (EE ∪ EB) := by
    intro z hz
    by_contra h
    simp only [EM,EL,ER,EE,EB,Set.mem_union,Set.mem_setOf_eq,not_or,not_not] at h
    exact hz ⟨h.1.1.1,h.1.1.2,h.1.2,h.2.1,h.2.2⟩
  calc
    _ ≤ μ (((EM ∪ EL) ∪ ER) ∪ (EE ∪ EB)) := measure_mono hsub
    _ ≤ ((μ EM+μ EL)+μ ER)+(μ EE+μ EB) :=
      (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) (measure_union_le _ _))
    _ ≤ ((2*BN+12*BM+2*BF)+2*BF)+(2*BE+2*BB) :=
      add_le_add (add_le_add (add_le_add hm hl) hr) (add_le_add he hb')
    _ = _ := by dsimp [BN,BM,BF,BE,BB]; ring

end
end StartupMarked
