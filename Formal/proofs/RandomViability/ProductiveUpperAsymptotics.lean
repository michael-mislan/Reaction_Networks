import proofs.RandomViability.ProductiveVolumeAsymptotics
import proofs.PowerLawSmallRAF.BinaryReactionEnumeration

namespace RandomViability
open Filter Topology PowerLawSmallRAF RAF.Polymer
noncomputable section
set_option maxHeartbeats 40000

def productiveUpperCoefficient (V : ℕ) : ℝ :=
  (Fintype.card (Molecule (10*V))*Fintype.card (Reaction (10*V+2)) : ℕ)

theorem productive_upper_log_negligible :
    Tendsto (fun n => Real.log (productiveUpperCoefficient (productiveVolume n))/(n : ℝ))
      atTop (𝓝 0) := by
  let k : ℕ → ℕ := fun n => 10*productiveVolume n
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [productive_volume_tendsto.eventually (eventually_ge_atTop b)] with n hn
    dsimp [k]
    omega
  have hkr : Tendsto (fun n => k n+2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hk.eventually (eventually_ge_atTop b)] with n hn
    omega
  have hkd : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
    have ht := productive_volume_div_nat.const_mul 10
    simp only [mul_zero] at ht
    convert ht using 1
    funext n
    simp only [k,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hkrd : Tendsto (fun n => ((k n+2 : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
    have hc := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have hh := hkd.add hc
    simp only [zero_add] at hh
    convert hh using 1
    funext n
    simp only [Nat.cast_add,Nat.cast_ofNat]
    ring
  have hM := (log_sourceMoleculeCount_normalized.comp hk).mul hkd
  have hR := (log_sourceReactionCount_normalized.comp hkr).mul hkrd
  have hh := hM.add hR
  simp only [mul_zero,zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hV := productive_volume_ge n
  have hk1 : 1 ≤ k n := by dsimp [k]; omega
  have hkn : (k n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk1)
  have hkrn : ((k n+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmpos : 0 < sourceMoleculeCount (k n) :=
    (show 0 < 2^(k n) by positivity).trans_le (sourceMoleculeCount_bounds hk1).1
  have hm0 : (sourceMoleculeCount (k n) : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hr0 : (sourceReactionCount (k n+2) : ℝ) ≠ 0 := by
    exact_mod_cast (show sourceReactionCount (k n+2) ≠ 0 by unfold sourceReactionCount; omega)
  change (Real.log (sourceMoleculeCount (k n) : ℝ)/(k n : ℝ))*((k n : ℝ)/(n : ℝ))+
    (Real.log (sourceReactionCount (k n+2) : ℝ)/((k n+2 : ℕ) : ℝ))*
      (((k n+2 : ℕ) : ℝ)/(n : ℝ)) = _
  change _ = Real.log ((Fintype.card (Molecule (k n))*Fintype.card (Reaction (k n+2)) : ℕ) : ℝ)/(n : ℝ)
  rw [card_binaryMolecule_eq_sourceMoleculeCount,card_binaryReaction_eq_sourceReactionCount (by omega)]
  simp only [Nat.cast_mul]
  rw [Real.log_mul hm0 hr0]
  field_simp

end
end RandomViability
