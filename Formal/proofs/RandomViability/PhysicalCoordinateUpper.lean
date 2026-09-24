import proofs.RandomViability.PhysicalCoordinateDrift
import proofs.RandomViability.NonfoodTargetCreation
import proofs.RandomViability.ShortTargetTailGain
import proofs.RandomViability.MixedIncidenceDriftBound

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 80000

theorem physical_coordinate_drift_upper {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ) (q : Molecule n) :
    physicalCoordinateDrift c V basal cat N q ≤
      (if molLength q ≤ 2 then 1 else 0)-(N q : ℝ)/V+
      collectiveGain (collectivePairSpeed c (fun r => basal r) (fun r z => cat r z)
        (fun z => (N z : ℝ)/V)) (fun z => (N z : ℝ)/V) q := by
  rw [physical_coordinate_drift_decomposition c V hV basal cat N q]
  apply add_le_add le_rfl
  unfold collectiveGain
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r _
  have hf := physical_pair_flux_envelope c V hV basal cat N r true
  have hb := physical_pair_flux_envelope c V hV basal cat N r false
  have hf0 := physical_pair_flux_nonneg c V basal cat N r true
  have hb0 := physical_pair_flux_nonneg c V basal cat N r false
  simp only [↓reduceIte,Bool.false_eq_true] at hf hb
  unfold reactionCoordinateChange singleCount
  simp only [eq_comm (a := q)]
  split_ifs <;> norm_num <;> nlinarith only [hf,hb,hf0,hb0]

theorem collective_gain_add {n : ℕ} (s t : Reaction n → ℝ) (x : Molecule n → ℝ)
    (p : Molecule n) : collectiveGain (fun r => s r+t r) x p =
      collectiveGain s x p+collectiveGain t x p := by
  unfold collectiveGain
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> ring

theorem collective_gain_mono {n : ℕ} (s t : Reaction n → ℝ) (hst : ∀ r,s r ≤ t r)
    (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q) (p : Molecule n) :
    collectiveGain s x p ≤ collectiveGain t x p := by
  unfold collectiveGain
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r _
  have hf := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hst r) (hx (reactionLeft r))) (hx (reactionRight r))
  have hb := mul_le_mul_of_nonneg_right (hst r) (hx (reactionProduct r))
  split_ifs <;> nlinarith only [hf,hb]

theorem basal_nonfood_target_gain_eleven {n : ℕ} (basal : Reaction n → ℝ)
    (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q) (hL : polymerMass x ≤ 11)
    (eps : ℝ) (heps : 0 ≤ eps) (hb : ∀ r,basal r ≤ 4*eps)
    (z : Molecule n) (hz : 2 < molLength z) :
    collectiveGain basal x z ≤ (550/3)*eps := by
  have hm := collective_gain_mono basal (fun _ => 4*eps) hb x hx z
  have hf := fixed_nonfood_forward_creation z hz x hx
  have hr := fixed_nonfood_cleavage_creation z hz x hx
  have hL0 : 0 ≤ polymerMass x := Finset.sum_nonneg (fun q _ => mul_nonneg (Nat.cast_nonneg _) (hx q))
  have hL2 := pow_le_pow_left₀ hL0 hL 2
  let F := ∑ r : Reaction n,if reactionProduct r = z then x (reactionLeft r)*x (reactionRight r) else 0
  let R := (∑ r : Reaction n,if reactionLeft r = z then x (reactionProduct r) else 0)+
    (∑ r : Reaction n,if reactionRight r = z then x (reactionProduct r) else 0)
  have hs : F+R ≤ 275/6 := by dsimp [F,R]; nlinarith only [hf,hr,hL,hL2]
  have hscaled := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4*eps)
  have he : collectiveGain (fun _ : Reaction n => 4*eps) x z = 4*eps*(F+R) := by
    unfold collectiveGain F R
    rw [mul_add,mul_add,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> ring
  rw [he] at hm
  nlinarith only [hm,hscaled]

/-- Sharpened outsider-coordinate forcing in the actual falling-factorial
reactor, including its negative unit-dilution term. -/
theorem short_free_nonfood_coordinate_upper {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (hfree : ¬ShortIncidence singleIncidenceCutoff c)
    (z : Molecule n) (hz : 2 < molLength z) (hsmall : molLength z ≤ singleIncidenceCutoff+2)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hcat : ∀ r q,(cat r q : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V) :
    physicalCoordinateDrift c V basal cat N z ≤
      (550/3 : ℝ)*(1/500000000)+29040/1000000000000-(N z : ℝ)/V := by
  let x : Molecule n → ℝ := fun q => (N q : ℝ)/V
  have hx : ∀ q,0 ≤ x q := fun q => by dsimp [x]; positivity
  have hL : polymerMass x ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).2 hM
  have hL0 : 0 ≤ polymerMass x := Finset.sum_nonneg (fun q _ => mul_nonneg (Nat.cast_nonneg _) (hx q))
  have hbGain := basal_nonfood_target_gain_eleven (fun r => (basal r : ℝ)) x hx hL
    (1/500000000) (by norm_num) hb z hz
  have hcGain := short_free_target_catalytic_gain c hfree (fun r q => (cat r q : ℝ)) x hx
    16 (by norm_num) hcat z hsmall
  have hL2 := pow_le_pow_left₀ hL0 hL 2
  have hL3 := pow_le_pow_left₀ hL0 hL 3
  have hspeed : collectivePairSpeed c (fun r => (basal r : ℝ)) (fun r q => (cat r q : ℝ)) x =
      fun r => (basal r : ℝ)+collectivePairSpeed c (fun _ => 0) (fun r q => (cat r q : ℝ)) x r := by
    funext r
    simp only [collectivePairSpeed,zero_add]
  have hh := physical_coordinate_drift_upper c V hV basal cat N z
  change physicalCoordinateDrift c V basal cat N z ≤
    (if molLength z ≤ 2 then 1 else 0)-(N z : ℝ)/V+
      collectiveGain (collectivePairSpeed c (fun r => basal r) (fun r q => cat r q) x) x z at hh
  rw [if_neg (not_le.mpr hz),hspeed,collective_gain_add] at hh
  norm_num [singleIncidenceCutoff] at hcGain
  norm_num at hL2 hL3
  nlinarith only [hh,hbGain,hcGain,hL2,hL3]

end
end RandomViability
