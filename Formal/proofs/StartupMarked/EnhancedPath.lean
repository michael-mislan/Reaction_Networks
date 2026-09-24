import proofs.RepeatedFunction.Mission
import proofs.StartupMarked.QuotaExport

namespace StartupMarked
open Classical RandomViability StartupCount Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 150000

def enhancedMission {n : ℕ} (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  twoWindowMission V z ∧ ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 199 →
    ∃ J K, prefixElapsed J (Preorder.frestrictLe J z) ≤ a ∧
      a < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧
      prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ b ∧
      b < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z) ∧
      ((19/10)*(b-a)-82)/624-1/20 < markedWindowReward (fun _ => exportReward V) z J K

theorem startup_enhanced_mission {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcatCap : ∀ r q,(cat r q : ℝ) ≤ 16)
    (hfood : ∀ q,molLength q ≤ 2 → c q = ∅) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinitM : (countMass (z 0).1 : ℝ)/V ≤ 10)
    (hinitL : ((z 0).1 (reactionLeft r) : ℝ)/V = 1)
    (hinitR : ((z 0).1 (reactionRight r) : ℝ)/V = 1)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hpositive : ∀ i,0 < (z (i+1)).2.2)
    (hd : Tendsto (fun K => prefixElapsed K (Preorder.frestrictLe K z)) atTop atTop)
    (hnoiseM : massNoiseBound c V basal cat 200 (1/4) z)
    (hnoiseL : coordinateNoiseBound c V basal cat (reactionLeft r) 200 (1/100000) z)
    (hnoiseR : coordinateNoiseBound c V basal cat (reactionRight r) 200 (1/100000) z)
    (hgood : z ∉ lowDuring (countGuard V r) (fun N => N (reactionProduct r)) (stockThreshold V) 1 199)
    (hnoiseMarked : markedRewardNoiseBound c V basal cat (cutoffReward V r stockCutoff) 200 15 z)
    (hnoiseE : markedRewardNoiseBound c V basal cat (fun _ => exportReward V) 200 (1/40) z)
    (hnoiseF : markedRewardNoiseBound c V basal cat (fun _ => grossFeedReward V) 200 1 z) :
    enhancedMission V z := by
  have hv : 0 < (V : ℝ) := by linarith
  have hh : ∀ i,0 ≤ (z (i+1)).2.2 := fun i => (hpositive i).le
  have hm := prefix_elapsed_monotone z hh
  have hguard (L : ℕ) (hL : prefixElapsed L (Preorder.frestrictLe L z) ≤ 199) :
      ∀ i ≤ L,countGuard V r (z i).1 :=
    source_guard_prefix hn c V hv basal cat r hb hcatCap hfood hl hr z hinitM hinitL hinitR hc hh
      hnoiseM hnoiseL hnoiseR L hL
  have hmass : ∀ i,prefixElapsed i (Preorder.frestrictLe i z) ≤ 199 →
      (countMass (z i).1 : ℝ) ≤ 11*V := fun i hi => (hguard i hi i le_rfl).1
  have hquota : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 199 →
      ∃ J K, prefixElapsed J (Preorder.frestrictLe J z) ≤ a ∧
        a < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧
        prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ b ∧
        b < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z) ∧
        ((19/10)*(b-a)-82)/624-1/20 < markedWindowReward (fun _ => exportReward V) z J K := by
    intro a b ha hab hbTime
    obtain ⟨J,K,hj,hj',hk,hk'⟩ := exists_time_window_indices z hh hd a b (by linarith) hab
    refine ⟨J,K,hj,hj',hk,hk',?_⟩
    exact source_window_export_quota hn c V hV basal cat r hb hcatCap hfood hl hr hlen huw huz hwz
      hsel hcat z J K a b ha hab hbTime hj hj' hk hk' hpositive hc
      (hguard (J+K) (hk.trans hbTime)) hgood hnoiseMarked hnoiseE
  refine ⟨?_,hquota⟩
  have hready (t : ℝ) (ht : 1 ≤ t) (ht' : t ≤ 199) (L : ℕ)
      (hpre : prefixElapsed L (Preorder.frestrictLe L z) ≤ t)
      (hpost : t < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z)) : observedReady V (z L).1 := by
    have hM := physical_mass_localization hn c V hv basal cat 200 z hinitM hc hh hnoiseM L
      (by linarith only [hpre,ht'])
    have hP := stock_at_holding V hv r z L t ht ht' (hguard L (hpre.trans ht'))
      (fun j hj => (hm hj).trans hpre) hpost hgood
    exact ⟨hM,reactionProduct r,hlen,hP⟩
  have hw (a b : ℝ) (ha : 1 ≤ a) (hbTime : b ≤ 199) (hdur : b-a = 99) : windowOutputReady V a b z := by
    obtain ⟨J,K,hj,hj',hk,hk'⟩ := exists_time_window_indices z hh hd a b (by linarith) (by linarith)
    have he := source_window_export hn c V hV basal cat r hb hcatCap hfood hl hr hlen huw huz hwz
      hsel hcat z J K a b ha hdur hbTime hj hj' hk hk' hpositive hc
      (hguard (J+K) (hk.trans hbTime)) hgood hnoiseMarked hnoiseE
    exact ⟨J,K,hj,hj',hk,hk',he,hready b (by linarith) hbTime (J+K) hk hk'⟩
  have hw1 := hw 1 100 (by norm_num) (by norm_num) (by norm_num)
  have hw2 := hw 100 199 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hmass,hw1,hw2,?_⟩
  obtain ⟨J,K,_,_,hk,hk',_,_⟩ := hw2
  have hM : ∀ i ≤ J+K,(countMass (z i).1 : ℝ) ≤ 11*V :=
    fun i hi => hmass i ((hm hi).trans hk)
  have hactive : ∀ i ≤ J+K,¬censoredNonfoodStop V 200 (massExitStop V) i (Preorder.frestrictLe i z) := by
    intro i hi
    exact mass_exit_active_before_first_exit V 200 z (by omega : i < J+K+1)
      (fun j hj => hM j (by omega)) ((hm hi).trans_lt (by linarith only [hk]))
  have hcomplete : ∀ i < J+K,(z (i+1)).2.2 ≤ 200-prefixElapsed i (Preorder.frestrictLe i z) := by
    intro i hi
    have he := (hm (show i+1 ≤ J+K by omega)).trans hk
    dsimp only at he
    rw [prefixElapsed_restrict_succ] at he
    linarith only [he]
  have hb0 : 0 ≤ 199-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) := sub_nonneg.mpr hk
  have hbcap : 199-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤
      min (z (J+K+1)).2.2 (200-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) := by
    apply le_min
    · rw [prefixElapsed_restrict_succ] at hk'
      linarith only [hk']
    · linarith
  have hbudget := marked_reward_budget c V basal cat (fun _ => grossFeedReward V)
    200 199 1 6 z (J+K) hactive hcomplete hh hb0 hbcap
    (fun i _ => (gross_feed_drift hn c V hv basal cat (z i).1).le) hnoiseF
  norm_num at hbudget
  refine ⟨⟨J+K,hk,hk',hbudget⟩,?_⟩
  obtain ⟨I,L,hi,hi',_,_⟩ := exists_time_window_indices z hh hd 1 1 (by norm_num) le_rfl
  exact ⟨I,hi,hi',hready 1 le_rfl (by norm_num) I hi hi'⟩

end
end StartupMarked
