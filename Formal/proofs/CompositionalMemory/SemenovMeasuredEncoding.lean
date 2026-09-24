import proofs.CompositionalMemory.SemenovOffspringKernel

namespace CompositionalMemory.Semenov
open scoped ENNReal

def measuredDecoder (n : Fin 8 → ℕ) : Bool := decide (120000000000000000 < n 1+n 2+n 3)

def initialMeasuredCounts : Bool → Fin 8 → ℕ
  | false => SemenovLowEndpoint.initialCounts
  | true => SemenovHighEndpoint.initialCounts

theorem terminal_decoder_margin (high : Bool) :
    if high then (1/200 : ℝ) <
      ((terminalRecoveryPiece high).zRight 1 : ℝ)+(terminalRecoveryPiece high).zRight 2+
        (terminalRecoveryPiece high).zRight 3-3*(terminalRecoveryPiece high).radius
    else ((terminalRecoveryPiece high).zRight 1 : ℝ)+(terminalRecoveryPiece high).zRight 2+
        (terminalRecoveryPiece high).zRight 3+3*(terminalRecoveryPiece high).radius < (1/200 : ℝ) := by
  cases high
  · have hh := Rat.cast_strictMono (K := ℝ) SemenovLowEndpoint.finite_checks.2.2.2.2.2.2.2.2.2
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div,Rat.cast_one] using hh
  · have hh := Rat.cast_strictMono (K := ℝ) SemenovHighEndpoint.finite_checks.2.2.2.2.2.2.2.2.2
    simpa only [Rat.cast_sub,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div,Rat.cast_one] using hh

theorem good_parent_decoder (high : Bool) (n : Fin 8 → ℕ) (hn : GoodRecoveryParent high n) :
    measuredDecoder n=high := by
  have hr : (0 : ℝ) ≤ (terminalRecoveryPiece high).radius := by
    exact_mod_cast (terminalRecoveryPiece high).geometry.1.2.1.le
  have hb := terminal_thiol_bounds _ _ _ hr (parent_region_radius high n hn)
  have hm := terminal_decoder_margin high
  have hv : (0 : ℝ) < recoveryVolume := by norm_num [recoveryVolume]
  have he : (n 1 : ℝ)/(recoveryVolume : ℝ)+(n 2 : ℝ)/(recoveryVolume : ℝ)+
      (n 3 : ℝ)/(recoveryVolume : ℝ)=((n 1+n 2+n 3 : ℕ) : ℝ)/(recoveryVolume : ℝ) := by
    push_cast
    ring
  change _ ≤ (n 1 : ℝ)/(recoveryVolume : ℝ)+(n 2 : ℝ)/(recoveryVolume : ℝ)+
    (n 3 : ℝ)/(recoveryVolume : ℝ) ∧
    (n 1 : ℝ)/(recoveryVolume : ℝ)+(n 2 : ℝ)/(recoveryVolume : ℝ)+
    (n 3 : ℝ)/(recoveryVolume : ℝ) ≤ _ at hb
  rw [he] at hb
  cases high
  · simp only [Bool.false_eq_true,if_false] at hm
    have hs := (div_lt_iff₀ hv).mp (hb.2.trans_lt hm)
    norm_num [recoveryVolume] at hs
    have hi : n 1+n 2+n 3 ≤ 120000000000000000 := by exact_mod_cast hs.le
    simp only [measuredDecoder,decide_eq_false_iff_not]
    exact not_lt.mpr hi
  · simp only [if_true] at hm
    have hs := (lt_div_iff₀ hv).mp (hm.trans_le hb.1)
    norm_num [recoveryVolume] at hs
    have hi : 120000000000000000 < n 1+n 2+n 3 := by exact_mod_cast hs
    simp only [measuredDecoder,decide_eq_true_eq]
    exact hi

theorem rational_parent_energy_cast (P : Fin 8 → Fin 8 → ℚ) (z : Fin 8 → ℚ)
    (n : Fin 8 → ℕ) (v : ℕ) :
    ((∑ i,∑ j,P i j*((n i : ℚ)/(v : ℚ)-z i)*((n j : ℚ)/(v : ℚ)-z j) : ℚ) : ℝ)=
      matrixEnergy (rationalMatrix P) ((fun j => (n j : ℝ)/(v : ℝ))-(fun j => (z j : ℝ))) := by
  simp only [Rat.cast_sum,Rat.cast_mul,Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,
    matrixEnergy,rationalMatrix,Pi.sub_apply]

theorem initial_measured_parent_good (high : Bool) : GoodRecoveryParent high (initialMeasuredCounts high) := by
  cases high
  · have hh := Rat.cast_mono (K := ℝ) SemenovLowEndpoint.initial_encoder_checks.1
    change ((∑ i,∑ j,SemenovLowMetric15.pr i j*
      ((SemenovLowEndpoint.initialCounts i : ℚ)/24000000000000000000-SemenovLowMetric15.zr i)*
      ((SemenovLowEndpoint.initialCounts j : ℚ)/24000000000000000000-SemenovLowMetric15.zr j) : ℚ) : ℝ) ≤ _ at hh
    have hc := rational_parent_energy_cast SemenovLowMetric15.pr SemenovLowMetric15.zr
      SemenovLowEndpoint.initialCounts 24000000000000000000
    simp only [Nat.cast_ofNat] at hc
    rw [hc] at hh
    unfold GoodRecoveryParent
    rw [show (recoveryEta false : ℝ)=(SemenovLowMetric15.eta : ℝ) by
      norm_num [recoveryEta,SemenovLowMetric15.eta]]
    exact hh
  · have hh := Rat.cast_mono (K := ℝ) SemenovHighEndpoint.initial_encoder_checks.1
    change ((∑ i,∑ j,SemenovHighMetric21.pr i j*
      ((SemenovHighEndpoint.initialCounts i : ℚ)/24000000000000000000-SemenovHighMetric21.zr i)*
      ((SemenovHighEndpoint.initialCounts j : ℚ)/24000000000000000000-SemenovHighMetric21.zr j) : ℚ) : ℝ) ≤ _ at hh
    have hc := rational_parent_energy_cast SemenovHighMetric21.pr SemenovHighMetric21.zr
      SemenovHighEndpoint.initialCounts 24000000000000000000
    simp only [Nat.cast_ofNat] at hc
    rw [hc] at hh
    exact hh

theorem initial_measured_count_cap (high : Bool) : ∀ j,initialMeasuredCounts high j ≤ recoveryCountCap := by
  cases high
  · exact SemenovLowEndpoint.initial_encoder_checks.2.2
  · exact SemenovHighEndpoint.initial_encoder_checks.2.2

noncomputable def initialMeasuredState (high : Bool) : GoodRecoveryState high := by
  classical
  refine ⟨encodeReactor recoveryCountCap recoveryFeedQuota (initialMeasuredCounts high) 0,?_⟩
  have hK : 0 < recoveryFeedQuota := by norm_num [recoveryFeedQuota]
  rw [encodeReactor,dif_pos ⟨initial_measured_count_cap high,hK⟩]
  exact if_pos (initial_measured_parent_good high)

theorem measured_explicit_first_division (high : Bool) :
    (99/100 : ℝ) ≤ bothDaughtersProbability high (initialMeasuredCounts high) :=
  (by norm_num : (99/100 : ℝ) ≤ (124/125 : ℝ)).trans
    (both_daughters_bound high _ (initial_measured_parent_good high))

theorem measured_explicit_ten_divisions (high : Bool) :
    (9/10 : ℝ≥0∞) ≤ (measuredOffspringKernel high).survival 10 (initialMeasuredState high) :=
  measured_ten_divisions high _

end CompositionalMemory.Semenov
