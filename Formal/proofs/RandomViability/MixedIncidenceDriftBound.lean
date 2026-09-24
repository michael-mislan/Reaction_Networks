import proofs.RandomViability.SingleIncidenceDriftEnvelope

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 90000

theorem collective_loss_add {n : ℕ} (s t : Reaction n → ℝ) (x : Molecule n → ℝ)
    (p : Molecule n) : collectiveLoss (fun r => s r+t r) x p =
      collectiveLoss s x p+collectiveLoss t x p := by
  unfold collectiveLoss
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> ring

theorem basal_target_loss_eleven {n : ℕ} (basal : Reaction n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q) (hL : polymerMass x ≤ 11)
    (eps : ℝ) (heps : 0 ≤ eps) (hb : ∀ r,basal r ≤ 4*eps) (p : Molecule n) :
    collectiveLoss basal x p ≤ 1012*eps := by
  have hl := collective_loss_bound basal x hx (4*eps) (by positivity) hb p
  have hpL := coordinate_mass_le x hx p
  have hp1 : (1 : ℝ) ≤ molLength p := by
    exact_mod_cast (show 1 ≤ molLength p by simp [molLength])
  have hxL : x p ≤ polymerMass x := by nlinarith only [hpL,mul_le_mul_of_nonneg_right hp1 (hx p)]
  have hx11 : x p ≤ 11 := hxL.trans hL
  have hprod : polymerMass x*x p ≤ 121 := by
    have hh := mul_le_mul hL hx11 (hx p) (by norm_num : (0 : ℝ) ≤ 11)
    norm_num at hh
    exact hh
  have hparen : (2*polymerMass x+(molLength p-1))*x p ≤ 253 := by
    nlinarith only [hpL,hL,hprod,hx p]
  have hh := mul_le_mul_of_nonneg_left hparen (by positivity : 0 ≤ 4*eps)
  nlinarith only [hl,hh]

def singleIncidenceCutoff : ℕ := 1000000000000
def singleIncidenceHalfCutoff : ℕ := 500000000000

/-- The uniform drift input required by the mixed-case stochastic adapter,
now derived from absence of every remaining local incidence. -/
theorem short_free_half_modified_drift_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (hfree : ¬ShortIncidence singleIncidenceCutoff c)
    (p : Molecule n) (hp : molLength p ≤ singleIncidenceHalfCutoff) (hp3 : 3 ≤ molLength p)
    (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V) :
    markedRewardDrift c V basal cat (halfModifiedInputReward p a V) N ≤ 1/200000 := by
  let x : Molecule n → ℝ := fun q => (N q : ℝ)/V
  have hx : ∀ q,0 ≤ x q := fun q => by dsimp [x]; positivity
  have hL : polymerMass x ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).2 hM
  have hL0 : 0 ≤ polymerMass x := Finset.sum_nonneg (fun q _ => mul_nonneg (Nat.cast_nonneg _) (hx q))
  have hbase := positive_basal_reward_drift c V hV basal cat N (1/500000000) (by norm_num) hb hM
  have hinput := positive_catalytic_drift_short_bound c hfree V hV basal cat N hM hcat
  have hbaseloss := basal_target_loss_eleven (fun r => (basal r : ℝ)) x hx hL
    (1/500000000) (by norm_num) hb p
  have hcatloss := short_free_target_catalytic_loss
    (k := singleIncidenceHalfCutoff) c hfree (fun r z => (cat r z : ℝ)) x hx
    16 (by norm_num) hcat p hp hp3
  have hL2 := pow_le_pow_left₀ hL0 hL 2
  have hL3 := pow_le_pow_left₀ hL0 hL 3
  have hcatloss' : (1000000000000 : ℝ)*
      collectiveLoss (collectivePairSpeed c (fun _ => 0) (fun r z => cat r z) x) x p ≤ 44528 := by
    norm_num [singleIncidenceHalfCutoff] at hcatloss
    norm_num at hL2 hL3
    nlinarith only [hcatloss,hL2,hL3]
  have hloss : collectiveLoss (collectivePairSpeed c (fun r => basal r) (fun r z => cat r z) x) x p ≤
      1012*(1/500000000 : ℝ)+44528/1000000000000 := by
    have hspeed : collectivePairSpeed c (fun r => (basal r : ℝ)) (fun r z => (cat r z : ℝ)) x =
        fun r => (basal r : ℝ)+collectivePairSpeed c (fun _ => 0) (fun r z => (cat r z : ℝ)) x r := by
      funext r
      simp only [collectivePairSpeed,zero_add]
    rw [hspeed,collective_loss_add]
    linarith only [hbaseloss,hcatloss']
  have henvelope := half_modified_drift_le_envelopes p a ha c V hV basal cat N
  have hweighted := mul_le_mul_of_nonneg_left hloss ha
  have hcap := mul_le_mul_of_nonneg_right ha2
    (by norm_num : (0 : ℝ) ≤ 1012*(1/500000000 : ℝ)+44528/1000000000000)
  norm_num [singleIncidenceCutoff] at hinput
  change (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*positiveBasalReward V N ch) ≤ _ at hbase
  change 2*markedRewardDrift c V basal cat (halfModifiedInputReward p a V) N ≤
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*positiveBasalReward V N ch)+
      markedRewardDrift c V basal cat (normalizedPositiveCatalyticReward V) N+
      a*collectiveLoss (collectivePairSpeed c (fun r => basal r) (fun r z => cat r z) x) x p at henvelope
  nlinarith only [henvelope,hbase,hinput,hweighted,hcap]

/-- The local mixed channel is removed by an exact reward identity, then the
uniform nonlocal-host bound applies. No kinetic hypothesis is assumed here. -/
theorem isolated_mixed_half_modified_drift_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (z₀ : Molecule n) (r₀ : Reaction n)
    (hsingle : SingleLocalIncidence singleIncidenceCutoff c z₀ r₀)
    (hmixed : MixedFoodIncidence r₀)
    (hsmall : molLength (reactionProduct r₀) ≤ singleIncidenceHalfCutoff)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V) :
    markedRewardDrift c V basal cat
      (halfModifiedInputReward (reactionProduct r₀) (ligationNonfoodMassGain r₀) V) N ≤ 1/200000 := by
  rw [half_modified_drift_erase c z₀ r₀ V basal cat N]
  have hpars := mixed_incidence_weight_parameters r₀ hmixed
  have ha := (ligationNonfoodMassGain_bounds r₀).1
  have hp3 : 3 ≤ molLength (reactionProduct r₀) := by
    have hh : (3 : ℝ) ≤ molLength (reactionProduct r₀) := by linarith only [hpars.2,ha]
    exact_mod_cast hh
  exact short_free_half_modified_drift_bound (eraseLocalIncidence c z₀ r₀)
    (erase_local_has_no_short_incidence c z₀ r₀ hsingle) (reactionProduct r₀) hsmall hp3
    (ligationNonfoodMassGain r₀) ha hpars.1 V hV basal cat hb hcat N hM

end
end RandomViability
