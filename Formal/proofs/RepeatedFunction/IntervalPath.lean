import proofs.RepeatedFunction.IntervalExport
import proofs.RandomViability.MarkedFiniteEvent

namespace RandomViability
open Classical Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 150000

theorem physical_interval_output_and_endpoint {n : ℕ} (hn : 2 ≤ n)
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
    (A0 B0 T : ℝ) (hA0 : 1 ≤ A0) (hAB0 : A0 ≤ B0) (hT : B0 < T) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinitM : (countMass (z 0).1 : ℝ)/V ≤ 10)
    (hinitL : ((z 0).1 (reactionLeft r) : ℝ)/V = 1)
    (hinitR : ((z 0).1 (reactionRight r) : ℝ)/V = 1)
    (hinitP : ((z 0).1 (reactionProduct r) : ℝ)/V = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hd : Tendsto (fun K => prefixElapsed K (Preorder.frestrictLe K z)) atTop atTop)
    (hnoiseM : massNoiseBound c V basal cat T (1/4) z)
    (hnoiseL : coordinateNoiseBound c V basal cat (reactionLeft r) T (1/100000) z)
    (hnoiseR : coordinateNoiseBound c V basal cat (reactionRight r) T (1/100000) z)
    (hnoiseP : coordinateNoiseBound c V basal cat (reactionProduct r) T (1/300000000000000000000) z)
    (hduration : 79 ≤ B0-A0)
    (hnoiseE : markedRewardNoiseBound c V basal cat (fun _ => exportReward V) T (1/40) z) :
    ∃ J K,prefixElapsed J (Preorder.frestrictLe J z) ≤ A0 ∧
      A0 < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧
      prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ B0 ∧
      B0 < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z) ∧
      (1/10 : ℝ) < markedWindowReward (fun _ => exportReward V) z J K ∧
      (countMass (z (J+K)).1 : ℝ)/V ≤ 21/2 ∧
      (1/3000000000000000000 : ℝ) ≤ ((z (J+K)).1 (reactionProduct r) : ℝ)/V := by
  obtain ⟨J,K,hj,hj',hk,hk',hI⟩ := physical_interval_mass_from_noise hn c V hV
    basal cat hb hcatCap hfood r hl hr hlen huw huz hwz hsel hbas hcat
    A0 B0 T hA0 hAB0 hT z hinitM hinitL hinitR hinitP hc hh hd
    hnoiseM hnoiseL hnoiseR hnoiseP
  have hm := prefix_elapsed_monotone z hh
  have hmass : ∀ i ≤ J+K,(countMass (z i).1 : ℝ) ≤ 11*V := by
    intro i hi
    have hg := physical_mass_localization hn c V hV basal cat T z hinitM hc hh hnoiseM i
      ((hm hi).trans_lt (hk.trans_lt hT))
    have he := (div_le_iff₀ hV).mp hg
    nlinarith only [he,hV]
  have he := physical_interval_export_lower c V hV basal cat A0 B0 T (1/40)
    hT hAB0 z J K hj hj' hk hk' hh hmass hnoiseE
  have hout : (1/10 : ℝ) < markedWindowReward (fun _ => exportReward V) z J K := by
    apply interval_export_margin (B0-A0) _ _ hduration hI
    convert he using 1
    ring
  obtain ⟨L,hlb,hlb',hM,hP⟩ := physical_startup_at_every_time hn c V hV basal cat
    hb hcatCap hfood r hl hr hlen huw huz hwz hsel hbas hcat T z
    hinitM hinitL hinitR hinitP hc hh hd hnoiseM hnoiseL hnoiseR hnoiseP B0
    (hA0.trans hAB0) hT
  have hsame := holding_index_unique z hh L (J+K) B0 hlb hlb' hk hk'
  subst L
  exact ⟨J,K,hj,hj',hk,hk',hout,hM,hP⟩

end
end RandomViability
