import proofs.StartupMarked.WindowDock
import proofs.StartupMarked.QuotaOccupation
namespace StartupMarked
open Classical RandomViability StartupCount RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
theorem source_window_export_quota {n : ℕ} (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r q,(cat r q : ℝ) ≤ 16) (hfood : ∀ q,molLength q ≤ 2 → cfg q = ∅)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4) (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ cfg (reactionProduct r)) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ) (a b : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbTime : b ≤ 199)
    (hfirst : prefixElapsed J (Preorder.frestrictLe J z) ≤ a)
    (hfirstNext : a < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z))
    (hlast : prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ b)
    (hlastNext : b < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z))
    (hh : ∀ i,0 < (z (i+1)).2.2)
    (hconsistent : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hguard : ∀ j ≤ J+K,countGuard V r (z j).1)
    (hgood : z ∉ lowDuring (countGuard V r) (fun N => N (reactionProduct r)) (stockThreshold V) 1 199)
    (hnoise : markedRewardNoiseBound cfg V basal cat (cutoffReward V r stockCutoff) 200 15 z)
    (hnoiseE : markedRewardNoiseBound cfg V basal cat (fun _ => exportReward V) 200 (1/40) z) :
    (((19/10 : ℝ)*(b-a)-82)/624-1/20) < markedWindowReward (fun _ => exportReward V) z J K := by
  have hv : 0 < (V : ℝ) := by linarith
  have hm := prefix_elapsed_monotone z (fun i => (hh i).le)
  have hmass : ∀ j ≤ J+K,(countMass (z j).1 : ℝ) ≤ 11*V := fun j hj => (hguard j hj).1
  have hactive (i : ℕ) (hi : i ≤ K) :
      ¬censoredNonfoodStop V 200 (massExitStop V) (J+i) (Preorder.frestrictLe (J+i) z) :=
    mass_exit_active_before_first_exit V 200 z (show J+i < J+K+1 by omega)
      (fun j hj => hmass j (by omega))
      ((hm (show J+i ≤ J+K by omega)).trans_lt (by linarith only [hlast,hbTime]))
  have hA : a-prefixElapsed J (Preorder.frestrictLe J z) ≤
      min (z (J+1)).2.2 (200-prefixElapsed J (Preorder.frestrictLe J z)) := by
    apply le_min
    · have he := hfirstNext
      rw [prefixElapsed_restrict_succ] at he
      linarith only [he]
    · linarith only [hab,hbTime]
  have hB : b-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤
      min (z (J+K+1)).2.2 (200-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) := by
    apply le_min
    · have he := hlastNext
      rw [prefixElapsed_restrict_succ] at he
      linarith only [he]
    · linarith only [hbTime]
  have hfloor := good_count_window_floor V hv r z J K a b ha (by linarith) hbTime
    hfirstNext hlast hh hguard hgood
  have hi := source_window_occupation_quota hn cfg V hV basal cat r hb hc hfood hl hr hlen huw huz hwz
    hsel hcat z J K a b hab (by linarith) hfirstNext hlast (fun i => (hh i).le) hconsistent hactive hfloor
    (hnoise J _ (sub_nonneg.mpr hfirst) hA) (hnoise (J+K) _ (sub_nonneg.mpr hlast) hB)
  have he := physical_interval_export_lower cfg V hv basal cat a b 200 (1/40)
    (by linarith) (by linarith) z J K hfirst hfirstNext hlast hlastNext (fun i => (hh i).le) hmass hnoiseE
  change (((19/10 : ℝ)*(b-a)-82)/624) < physicalIntervalNonfoodIntegral V z J K a b at hi
  linarith only [hi,he]

end
end StartupMarked
