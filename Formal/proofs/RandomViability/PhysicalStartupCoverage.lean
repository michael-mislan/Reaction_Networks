import proofs.RandomViability.PhysicalTimeCoverage

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 100000

/-- Startup at every physical time before the noise horizon. Mass localization,
food floors, active prefixes and holding-interval coverage are derived here. -/
theorem physical_startup_at_every_time {n : ℕ} (hn : 2 ≤ n)
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
    (T : ℝ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
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
    (t : ℝ) (ht1 : 1 ≤ t) (htT : t < T) :
    ∃ K,prefixElapsed K (Preorder.frestrictLe K z) ≤ t ∧
      t < prefixElapsed (K+1) (Preorder.frestrictLe (K+1) z) ∧
      (countMass (z K).1 : ℝ)/V ≤ 21/2 ∧
      (1/3000000000000000000 : ℝ) ≤ ((z K).1 (reactionProduct r) : ℝ)/V := by
  obtain ⟨K,s,hbefore,hs0,hsh,hrepr,hafter⟩ :=
    unbounded_elapsed_partial_interval z hd t T (by linarith only [ht1]) htT.le
  have hm : ∀ i ≤ K,(countMass (z i).1 : ℝ)/V ≤ 21/2 := by
    intro i hi
    exact physical_mass_localization hn c V hV basal cat T z hinitM hc hh hnoiseM
      i ((hbefore i hi).trans_lt htT)
  have hgood : ∀ i < K+1,(countMass (z i).1 : ℝ) ≤ 11*V := by
    intro i hi
    have hv := (div_le_iff₀ hV).mp (hm i (by omega))
    nlinarith only [hv,hV]
  have hactive : ∀ i ≤ K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z) := by
    intro i hi
    exact mass_exit_active_before_first_exit V T z (by omega : i < K+1) hgood
      ((hbefore i hi).trans_lt htT)
  have hcomplete : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z) := by
    intro i hi
    have he := (hbefore (i+1) (by omega)).trans_lt htT
    rw [prefixElapsed_restrict_succ] at he
    linarith only [he]
  refine ⟨K,hbefore K le_rfl,hafter,hm K le_rfl,?_⟩
  exact physical_startup_product_from_noise c V hV basal cat hb hcatCap hfood r
    hl hr hlen huw huz hwz hsel hbas hcat T s z K hinitL hinitR hinitP hs0 hsh
    (fun i _ => hc i) hactive hcomplete (fun i _ => hh i) hnoiseL hnoiseR hnoiseP
    (by rw [hrepr]; exact ht1)

end
end RandomViability
