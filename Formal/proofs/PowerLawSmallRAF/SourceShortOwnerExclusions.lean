import proofs.PowerLawSmallRAF.SourceShortOwnerBound
import proofs.PowerLawSmallRAF.SourceOwnerLengthScales

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

theorem source_short_owner_failure_tendsto_of_ratio (m L : Nat → Nat)
    (hb : ∀ᶠ n : Nat in atTop, m n ≤ n ∧ 0 < L n)
    (hr : Tendsto (fun n : Nat => (n : ℝ)*(2 : ℝ)^(m n)/(L n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : Nat => sourceShortOwnerFailureMass (2-2/(n : ℝ)) n (m n) (L n))
      atTop (𝓝 0) := by
  have hu := hr.const_mul 4
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
      linarith
    apply Finset.sum_nonneg
    intro config _
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg _ _ ha config
    · exact le_rfl
  · filter_upwards [eventually_ge_atTop 4, hb, sourceTotalDegreeMean_eventually_le] with n hn hb hm
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
      linarith
    apply (source_short_owner_failure_le _ n (m n) (L n) ha hn hb.1 hb.2).trans
    calc
      _ ≤ (2 : ℝ)^(m n+1)*(2*(n : ℝ))/(L n : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) (Nat.cast_nonneg _)
      _ = _ := by rw [pow_succ]; ring

theorem sourceHighShortOwnerFailureMass_tendsto_zero :
    Tendsto (fun n : Nat => sourceShortOwnerFailureMass (2-2/(n : ℝ)) n
      (n-2*shrinkingBandWidth n) (sourceShrinkingLower n)) atTop (𝓝 0) := by
  apply source_short_owner_failure_tendsto_of_ratio
  · filter_upwards with n
    exact ⟨Nat.sub_le _ _, pow_pos (by decide) _⟩
  · apply nat_div_two_pow_shrinking_tendsto_zero.congr'
    have hs := shrinkingBandWidth_relative_tendsto (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
    filter_upwards [hs, eventually_ge_atTop 1] with n hs hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hh : 2*shrinkingBandWidth n ≤ n := by
      have h := (div_lt_iff₀ hnpos).mp hs
      have h' : (2 : ℝ)*(shrinkingBandWidth n : ℝ) ≤ n := by linarith
      exact_mod_cast h'
    have hp : (2 : ℝ)^(n-2*shrinkingBandWidth n)*(2 : ℝ)^(shrinkingBandWidth n) =
        (sourceShrinkingLower n : ℝ) := by
      rw [← pow_add]
      simp only [sourceShrinkingLower, Nat.cast_pow, Nat.cast_ofNat]
      congr 1
      omega
    rw [← hp]
    field_simp

theorem sourceLowShortOwnerFailureMass_tendsto_zero :
    Tendsto (fun n : Nat => sourceShortOwnerFailureMass (2-2/(n : ℝ)) n
      (n/200) (sourceLowBandLower n)) atTop (𝓝 0) := by
  apply source_short_owner_failure_tendsto_of_ratio
  · filter_upwards with n
    exact ⟨Nat.div_le_self _ _, pow_pos (by decide) _⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds nat_div_two_pow_twohundredth_tendsto_zero
    · filter_upwards with n
      positivity
    · filter_upwards with n
      have hpow : (2 : ℝ)^(2*(n/200)) ≤ (2 : ℝ)^(n/100) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      simp only [sourceLowBandLower, Nat.cast_pow, Nat.cast_ofNat]
      calc
        _ ≤ (n : ℝ)*(2 : ℝ)^(n/200)/(2 : ℝ)^(2*(n/200)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
        _ = _ := by
          rw [Nat.mul_comm 2 (n/200), pow_mul]
          field_simp

end
end PowerLawSmallRAF
