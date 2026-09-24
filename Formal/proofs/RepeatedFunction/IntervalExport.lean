import proofs.RepeatedFunction.IntervalMass
import proofs.RandomViability.MarkedProductiveOutput

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

/-- Convert an actual occupation integral to measured export on the same window.
Both partial holding intervals are included; no state is reset. -/
theorem physical_interval_export_lower {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (a b T eta : ℝ) (hT : b < T) (hab : a ≤ b)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ)
    (hfirst : prefixElapsed J (Preorder.frestrictLe J z) ≤ a)
    (hfirstNext : a < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z))
    (hlast : prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ b)
    (hlastNext : b < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hmass : ∀ i ≤ J+K,(countMass (z i).1 : ℝ) ≤ 11*V)
    (hnoise : markedRewardNoiseBound c V basal cat (fun _ => exportReward V) T eta z) :
    physicalIntervalNonfoodIntegral V z J K a b-2*eta ≤
      markedWindowReward (fun _ => exportReward V) z J K := by
  have hm := prefix_elapsed_monotone z hh
  have hactive : ∀ i ≤ J+K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z) := by
    intro i hi
    exact mass_exit_active_before_first_exit V T z (by omega : i < J+K+1)
      (fun j hj => hmass j (by omega)) ((hm hi).trans_lt (hlast.trans_lt hT))
  have hcomplete : ∀ i < J+K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z) := by
    intro i hi
    have he := (hm (show i+1 ≤ J+K by omega)).trans_lt (hlast.trans_lt hT)
    dsimp only at he
    rw [prefixElapsed_restrict_succ] at he
    linarith only [he]
  have ha : a-prefixElapsed J (Preorder.frestrictLe J z) ≤
      min (z (J+1)).2.2 (T-prefixElapsed J (Preorder.frestrictLe J z)) := by
    apply le_min
    · rw [prefixElapsed_restrict_succ] at hfirstNext
      linarith only [hfirstNext]
    · linarith only [hab,hT]
  have hb : b-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤
      min (z (J+K+1)).2.2 (T-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) := by
    apply le_min
    · rw [prefixElapsed_restrict_succ] at hlastNext
      linarith only [hlastNext]
    · linarith only [hT]
  have he := marked_reward_window_identity c V basal cat (fun _ => exportReward V) T
    (a-prefixElapsed J (Preorder.frestrictLe J z))
    (b-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) z J K
    (fun i hi => hactive (J+i) (by omega)) (fun i hi => hcomplete (J+i) (by omega))
  have hd (N : Molecule n → ℕ) :
      markedRewardDrift c V basal cat (fun _ => exportReward V) N =
      nonfoodMass (fun q => (N q : ℝ)/V) :=
    (export_reward_drift c V hV basal cat N).trans (count_nonfood_normalized N V)
  simp only [hd] at he
  change markedWindowReward (fun _ => exportReward V) z J K =
    physicalIntervalNonfoodIntegral V z J K a b +
    markedRewardWithinInterval c V basal cat (fun _ => exportReward V) T (massExitStop V)
      z (J+K) (b-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) -
    markedRewardWithinInterval c V basal cat (fun _ => exportReward V) T (massExitStop V)
      z J (a-prefixElapsed J (Preorder.frestrictLe J z)) at he
  have he0 := abs_le.mp (hnoise J _ (sub_nonneg.mpr hfirst) ha)
  have he1 := abs_le.mp (hnoise (J+K) _ (sub_nonneg.mpr hlast) hb)
  linarith only [he,he0.2,he1.1]

theorem interval_export_margin (duration integral output : ℝ)
    (hd : 79 ≤ duration)
    (hI : duration*((19/10 : ℝ)-480*(1/500000000 : ℝ))-54 ≤ 640*integral)
    (hE : integral-1/20 ≤ output) : 1/10 < output := by
  linarith only [hd,hI,hE]

end
end RandomViability
