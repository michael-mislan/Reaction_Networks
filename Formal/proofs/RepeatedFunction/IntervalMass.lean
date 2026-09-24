import proofs.RepeatedFunction.IntervalPotential

namespace RandomViability
open Classical Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 150000

theorem physical_interval_mass_from_noise {n : ℕ} (hn : 2 ≤ n)
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
    : ∃ J K,prefixElapsed J (Preorder.frestrictLe J z) ≤ A0 ∧
      A0 < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧
      prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ B0 ∧
      B0 < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z) ∧
      (B0-A0)*((19/10 : ℝ)-480*(1/500000000 : ℝ))-54 ≤
        640*physicalIntervalNonfoodIntegral V z J K A0 B0 := by
  obtain ⟨J,K,hfirst,hfirstNext,hlast,hlastNext⟩ :=
    exists_time_window_indices z hh hd A0 B0 (by linarith only [hA0]) hAB0
  have hm := prefix_elapsed_monotone z hh
  have hmass : ∀ i ≤ J+K,(countMass (z i).1 : ℝ) ≤ 11*V := by
    intro i hi
    have ht := (hm hi).trans_lt (hlast.trans_lt hT)
    have hg := physical_mass_localization hn c V hV basal cat T z hinitM hc hh hnoiseM i ht
    have he := (div_le_iff₀ hV).mp hg
    nlinarith only [he,hV]
  have hactive : ∀ i ≤ J+K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z) := by
    intro i hi
    exact mass_exit_active_before_first_exit V T z (by omega : i < J+K+1)
      (fun j hj => hmass j (by omega)) ((hm hi).trans_lt (hlast.trans_lt hT))
  have hfloor : ∀ i ≤ K,(1/3000000000000000000 : ℝ) ≤ ((z (J+i)).1 (reactionProduct r) : ℝ)/V := by
    intro i hi
    let s := max (1-prefixElapsed (J+i) (Preorder.frestrictLe (J+i) z)) 0
    have hidx : J+i ≤ J+K := by omega
    have htime : prefixElapsed (J+i) (Preorder.frestrictLe (J+i) z) < T :=
      (hm hidx).trans_lt (hlast.trans_lt hT)
    have hnext : 1 < prefixElapsed (J+i+1) (Preorder.frestrictLe (J+i+1) z) :=
      (lt_of_le_of_lt hA0 hfirstNext).trans_le (hm (by omega))
    have hs0 : 0 ≤ s := le_max_right _ _
    have hsw : s ≤ (z (J+i+1)).2.2 := by
      apply max_le
      · rw [prefixElapsed_restrict_succ] at hnext
        linarith only [hnext]
      · exact hh (J+i)
    have hsT : s ≤ T-prefixElapsed (J+i) (Preorder.frestrictLe (J+i) z) := by
      apply max_le
      · linarith only [hT,hAB0,hA0]
      · exact sub_nonneg.mpr htime.le
    have hcomplete : ∀ j < J+i,(z (j+1)).2.2 ≤ T-prefixElapsed j (Preorder.frestrictLe j z) := by
      intro j hj
      have he := (hm (show j+1 ≤ J+i by omega)).trans_lt htime
      dsimp only at he
      rw [prefixElapsed_restrict_succ] at he
      linarith only [he]
    exact physical_startup_product_from_noise c V hV basal cat hb hcatCap hfood r
      hl hr hlen huw huz hwz hsel hbas hcat T s z (J+i) hinitL hinitR hinitP hs0
      (le_min hsw hsT) (fun j _ => hc j) (fun j hj => hactive j (hj.trans hidx))
      hcomplete (fun j _ => hh j) hnoiseL hnoiseR hnoiseP
      (by have he := le_max_left (1-prefixElapsed (J+i) (Preorder.frestrictLe (J+i) z)) 0
          dsimp [s]; linarith only [he])
  have hg := physical_interval_potential_gain c V hV basal cat hb hcatCap hfood r
    hl hr hlen huw huz hwz hsel hbas hcat A0 B0 T hAB0 hT z J K hfirst hfirstNext hlast hlastNext
    hh hc hactive hfloor hnoiseL hnoiseR hnoiseP
  have ha0 : 0 ≤ A0-prefixElapsed J (Preorder.frestrictLe J z) := sub_nonneg.mpr hfirst
  have hb0 : 0 ≤ B0-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) := sub_nonneg.mpr hlast
  have ha : A0-prefixElapsed J (Preorder.frestrictLe J z) ≤
      min (z (J+1)).2.2 (T-prefixElapsed J (Preorder.frestrictLe J z)) := by
    apply le_min
    · rw [prefixElapsed_restrict_succ] at hfirstNext
      linarith only [hfirstNext]
    · linarith only [hT,hAB0,hA0]
  have hb' : B0-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤
      min (z (J+K+1)).2.2 (T-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) := by
    apply le_min
    · rw [prefixElapsed_restrict_succ] at hlastNext
      linarith only [hlastNext]
    · linarith only [hT,hAB0,hA0]
  have hp := physical_potential_endpoint_penalty c V hV basal cat r hlen T z J (J+K)
    (A0-prefixElapsed J (Preorder.frestrictLe J z))
    (B0-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z))
    (hactive J (by omega)) (hactive (J+K) le_rfl) ha0 hb0 ha hb'
    (by simpa only [Nat.add_zero] using hfloor 0 (by omega)) (hfloor K le_rfl)
    (hmass (J+K) le_rfl) hnoiseL hnoiseR hnoiseP
  refine ⟨J,K,hfirst,hfirstNext,hlast,hlastNext,?_⟩
  linarith only [hg,hp]

end
end RandomViability
