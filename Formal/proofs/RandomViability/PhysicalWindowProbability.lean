import proofs.RandomViability.PhysicalWindowMass

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
open scoped Topology ENNReal
noncomputable section
set_option maxHeartbeats 150000

def windowMassCertificate {n : ℕ} (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∃ J K,prefixElapsed J (Preorder.frestrictLe J z) ≤ 1 ∧
    1 < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧
    prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ 100 ∧
    100 < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z) ∧
    99*((19/10 : ℝ)-480*(1/500000000 : ℝ))-54 ≤
      640*physicalWindowNonfoodIntegral V z J K

def collectiveWindowCoverage {n : ℕ} (V : NNReal) (r : Reaction n) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  startupCoverage V r T z ∧ windowMassCertificate V z

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_collective_window_ae (hn : 2 ≤ n)
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
    (T : ℝ) (hTlarge : 100 < T) (N : Molecule n → ℕ)
    (hinitM : (countMass N : ℝ)/V ≤ 10)
    (hinitL : (N (reactionLeft r) : ℝ)/V = 1)
    (hinitR : (N (reactionRight r) : ℝ)/V = 1)
    (hinitP : (N (reactionProduct r) : ℝ)/V = 0)
    : ∀ᵐ z ∂physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N,
      massNoiseBound c V basal cat T (1/4) z →
      coordinateNoiseBound c V basal cat (reactionLeft r) T (1/100000) z →
      coordinateNoiseBound c V basal cat (reactionRight r) T (1/100000) z →
      coordinateNoiseBound c V basal cat (reactionProduct r) T (1/300000000000000000000) z →
      collectiveWindowCoverage V r T z := by
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
  have hw := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
  have hs := physical_startup_coverage_ae hn c V hV basal cat hb hcatCap hfood r
    hl hr hlen huw huz hwz hsel hbas hcat T N hinitM hinitL hinitR hinitP
  filter_upwards [hi,hc,hw,physical_prefix_times_diverge hn c V hV basal cat N,hs]
    with z hzi hzc hzw hzd hzs
  intro hM hL hR hP
  refine ⟨hzs hM hL hR hP,?_⟩
  exact physical_window_mass_from_noise hn c V hV basal cat hb hcatCap hfood r
    hl hr hlen huw huz hwz hsel hbas hcat T hTlarge z
    (by simpa only [hzi] using hinitM) (by simpa only [hzi] using hinitL)
    (by simpa only [hzi] using hinitR) (by simpa only [hzi] using hinitP)
    hzc hzw hzd hM hL hR hP

theorem physical_collective_window_failure_tail (hn : 4 ≤ n)
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
    (T : ℝ) (hTlarge : 100 < T) (N : Molecule n → ℕ)
    (hinitM : (countMass N : ℝ)/V ≤ 10)
    (hinitL : (N (reactionLeft r) : ℝ)/V = 1)
    (hinitR : (N (reactionRight r) : ℝ)/V = 1)
    (hinitP : (N (reactionProduct r) : ℝ)/V = 0)
    (δN δM δF δP : ℝ) (hδN : 0 < δN) (hδM : 0 < δM)
    (hδF : 0 < δF) (hδP : 0 < δP) (hT : 0 ≤ T)
    (hmN : δN+(n : ℝ)/V ≤ 1/8) (hmM : δM+2/V ≤ 1/80)
    (hmF : δF+2/V ≤ 1/100000) (hmP : δP+2/V ≤ 1/300000000000000000000) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ¬collectiveWindowCoverage V r T z} ≤
      2*ENNReal.ofReal (Real.exp (-(δN^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δN)))))+
      12*ENNReal.ofReal (Real.exp (-(δM^2*(V : ℝ)/(4*(96000*T+2*δM)))))+
      4*ENNReal.ofReal (Real.exp (-(δF^2*(V : ℝ)/(4*(96000*T+2*δF)))))+
      2*ENNReal.ofReal (Real.exp (-(δP^2*(V : ℝ)/(4*(96000*T+2*δP))))) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  let EM := {z | ¬massNoiseBound c V basal cat T (1/4) z}
  let EL := {z | ¬coordinateNoiseBound c V basal cat (reactionLeft r) T (1/100000) z}
  let ER := {z | ¬coordinateNoiseBound c V basal cat (reactionRight r) T (1/100000) z}
  let EP := {z | ¬coordinateNoiseBound c V basal cat (reactionProduct r) T (1/300000000000000000000) z}
  let BM := 2*ENNReal.ofReal (Real.exp (-(δN^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δN)))))+
    12*ENNReal.ofReal (Real.exp (-(δM^2*(V : ℝ)/(4*(96000*T+2*δM)))))
  let BF := 2*ENNReal.ofReal (Real.exp (-(δF^2*(V : ℝ)/(4*(96000*T+2*δF)))))
  let BP := 2*ENNReal.ofReal (Real.exp (-(δP^2*(V : ℝ)/(4*(96000*T+2*δP)))))
  have hbc : ∀ q,(basal q : ℝ) ≤ 1 := by
    intro q
    have hh := hb q
    linarith only [hh]
  have hgood := physical_collective_window_ae (by omega) c V hV basal cat hb hcatCap hfood r
    hl hr hlen huw huz hwz hsel hbas hcat T hTlarge N hinitM hinitL hinitR hinitP
  have hsub : ∀ᵐ z ∂μ,z ∈ {z | ¬collectiveWindowCoverage V r T z} → z ∈ ((EM ∪ EL) ∪ ER) ∪ EP := by
    filter_upwards [hgood] with z hz
    intro hbad
    by_contra h
    simp only [EM,EL,ER,EP,Set.mem_union,Set.mem_setOf_eq,not_or,not_not] at h
    exact hbad (hz h.1.1.1 h.1.1.2 h.1.2 h.2)
  have hM : μ EM ≤ BM := by
    have h := physical_mass_noise_failure hn c V hV basal cat N hbc hcatCap δN δM T
      (1/8) (1/80) hδN hδM hT hmN hmM
    have he : (1/8 : ℝ)+10*(1/80) = 1/4 := by norm_num
    rw [he] at h
    exact h
  have hL : μ EL ≤ BF := physical_noise_bound_failure (by omega) c V hV basal cat N hbc hcatCap
    (reactionLeft r) δF T (1/100000) hδF hT hmF
  have hR : μ ER ≤ BF := physical_noise_bound_failure (by omega) c V hV basal cat N hbc hcatCap
    (reactionRight r) δF T (1/100000) hδF hT hmF
  have hP : μ EP ≤ BP := physical_noise_bound_failure (by omega) c V hV basal cat N hbc hcatCap
    (reactionProduct r) δP T (1/300000000000000000000) hδP hT hmP
  calc
    _ ≤ μ (((EM ∪ EL) ∪ ER) ∪ EP) := measure_mono_ae hsub
    _ ≤ ((μ EM+μ EL)+μ ER)+μ EP :=
      (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ ((BM+BF)+BF)+BP := add_le_add (add_le_add (add_le_add hM hL) hR) hP
    _ = _ := by dsimp [BM,BF,BP]; ring


end
end RandomViability
