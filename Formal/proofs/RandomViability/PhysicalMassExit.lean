import proofs.RandomViability.MassNoiseProbability
import proofs.RandomViability.JumpInitial

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Actual-law mass exit bound at all represented jump times strictly before T.
Time coverage/nonexplosion is not part of this theorem. -/
theorem physical_mass_exit_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hinit : (countMass N : ℝ)/V ≤ 10)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r q,(cat r q : ℝ) ≤ 16)
    (δN δF T : ℝ) (hδN : 0 < δN) (hδF : 0 < δF) (hT : 0 ≤ T)
    (hmarginN : δN+(n : ℝ)/V ≤ 1/8) (hmarginF : δF+2/V ≤ 1/80) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ∃ K,prefixElapsed K (Preorder.frestrictLe K z) < T ∧
        11*(V : ℝ) < countMass (z K).1} ≤
      2*ENNReal.ofReal (Real.exp (-(δN^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δN)))))+
      12*ENNReal.ofReal (Real.exp (-(δF^2*(V : ℝ)/(4*(96000*T+2*δF))))) := by
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hw := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  apply le_trans (measure_mono_ae ?_)
    (physical_mass_noise_failure hn c V hV basal cat N hbasal hcat δN δF T (1/8) (1/80)
      hδN hδF hT hmarginN hmarginF)
  filter_upwards [hi,hc,hw] with z hzi hzc hzw
  rintro ⟨K,hK,hlarge⟩ hnoise
  have he : (1/8 : ℝ)+10*(1/80) = 1/4 := by norm_num
  rw [he] at hnoise
  have hb := physical_mass_localization (by omega) c V hV basal cat T z
    (by simpa only [hzi] using hinit) hzc hzw hnoise K hK
  have hb' := (div_le_iff₀ hV).mp hb
  nlinarith only [hb',hlarge,hV]

end
end RandomViability
