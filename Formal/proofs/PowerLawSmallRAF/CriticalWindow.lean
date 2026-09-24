import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Normed.Group.Tannery

namespace PowerLawSmallRAF

open Filter Topology

/-- The proposed critical-window profile, with its continuous value supplied
separately at the removable singularity `b=0`. -/
noncomputable def criticalLambda (b : ℝ) : ℝ :=
  if b = 0 then Real.log 2 / (Real.pi ^ 2 / 6)
  else (1 - Real.exp (-b * Real.log 2)) / (b * (Real.pi ^ 2 / 6))

@[simp] theorem criticalLambda_zero :
    criticalLambda 0 = Real.log 2 / (Real.pi ^ 2 / 6) := by
  simp [criticalLambda]

/-- At exponent exactly two, the growing harmonic numerator on the dyadic
polymer scale has the predicted normalized limit. -/
theorem harmonic_two_pow_normalized :
    Tendsto (fun n : Nat => (harmonic (2 ^ n) : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  have hpow : Tendsto (fun n : Nat => 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have herr :
      Tendsto (fun n : Nat =>
        (harmonic (2 ^ n) : ℝ) - Real.log ((2 ^ n : Nat) : ℝ))
        atTop (𝓝 Real.eulerMascheroniConstant) :=
    by
      convert Real.tendsto_harmonic_sub_log.comp hpow using 1
  have herrDiv := herr.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have htarget : Tendsto (fun n : Nat =>
      ((harmonic (2 ^ n) : ℝ) - Real.log ((2 ^ n : Nat) : ℝ)) /
        (n : ℝ) + Real.log 2)
      atTop (𝓝 (Real.log 2)) := by
    simpa only [zero_add] using herrDiv.add (tendsto_const_nhds :
      Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2)))
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  ring

/-- Exact source reaction-count formula used by the Zipf cap. -/
def sourceReactionCount (n : Nat) : Nat :=
  (n - 2) * 2 ^ (n + 1) + 4

theorem tendsto_log_nat_succ_div_nat :
    Tendsto (fun n : Nat => Real.log ((n + 1 : Nat) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : Nat => Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hshift : Tendsto (fun n : Nat =>
      Real.log ((n + 1 : Nat) : ℝ) / ((n + 1 : Nat) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).2 hbase
  have hratio : Tendsto (fun n : Nat => ((n + 1 : Nat) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).add
      ((tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).div_atTop
        (tendsto_natCast_atTop_atTop (R := ℝ)))
    have h' : Tendsto (fun n : Nat => (1 : ℝ) + 1 / (n : ℝ))
        atTop (𝓝 1) := by simpa only [add_zero] using h
    apply h'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    push_cast
    field_simp
  have hprod := hshift.mul hratio
  have hprod' : Tendsto (fun n : Nat =>
      (Real.log ((n + 1 : Nat) : ℝ) / ((n + 1 : Nat) : ℝ)) *
        (((n + 1 : Nat) : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_mul] using hprod
  apply hprod'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn10 : ((n + 1 : Nat) : ℝ) ≠ 0 := by positivity
  field_simp

theorem tendsto_nat_succ_div_nat :
    Tendsto (fun n : Nat => ((n + 1 : Nat) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).add
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h' : Tendsto (fun n : Nat => (1 : ℝ) + 1 / (n : ℝ))
      atTop (𝓝 1) := by simpa only [add_zero] using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  push_cast
  field_simp

theorem sourceReactionCount_bounds {n : Nat} (hn : 4 ≤ n) :
    2 ^ n ≤ sourceReactionCount n ∧
      sourceReactionCount n ≤ (n + 1) * 2 ^ (n + 1) := by
  unfold sourceReactionCount
  constructor
  · have hcoef : 1 ≤ n - 2 := by omega
    have hp : 2 ^ n ≤ 2 ^ (n + 1) := by
      rw [pow_succ]
      omega
    have hmul : 2 ^ (n + 1) ≤ (n - 2) * 2 ^ (n + 1) := by
      simpa using Nat.mul_le_mul_right (2 ^ (n + 1)) hcoef
    omega
  · have hpow : 4 ≤ 2 ^ (n + 1) := by
      have : 2 ^ 2 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at this ⊢
      exact this
    have hsub : n - 2 ≤ n := Nat.sub_le n 2
    have hmul := Nat.mul_le_mul_right (2 ^ (n + 1)) hsub
    calc
      (n - 2) * 2 ^ (n + 1) + 4 ≤ n * 2 ^ (n + 1) + 4 :=
        Nat.add_le_add_right hmul 4
      _ ≤ n * 2 ^ (n + 1) + 2 ^ (n + 1) :=
        Nat.add_le_add_left hpow _
      _ = (n + 1) * 2 ^ (n + 1) := by ring

theorem log_sourceReactionCount_normalized :
    Tendsto (fun n : Nat =>
      Real.log (sourceReactionCount n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  let upper : Nat → ℝ := fun n =>
    Real.log ((n + 1 : Nat) : ℝ) / (n : ℝ) +
      (((n + 1 : Nat) : ℝ) / (n : ℝ)) * Real.log 2
  have hu : Tendsto upper atTop (𝓝 (Real.log 2)) := by
    have hmul := tendsto_nat_succ_div_nat.mul
      (tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log 2)
        atTop (𝓝 (Real.log 2)))
    simpa [upper] using tendsto_log_nat_succ_div_nat.add hmul
  have hl : Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2)) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hb := (sourceReactionCount_bounds hn).1
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
    have hlog : Real.log ((2 ^ n : Nat) : ℝ) ≤
        Real.log (sourceReactionCount n : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact Set.mem_Ioi.mpr (by
          exact_mod_cast (lt_of_lt_of_le (pow_pos (by norm_num) n) hb))
      · exact_mod_cast hb
    calc
      Real.log 2 = Real.log ((2 ^ n : Nat) : ℝ) / (n : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        field_simp
      _ ≤ Real.log (sourceReactionCount n : ℝ) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right hlog (by positivity)
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hb := (sourceReactionCount_bounds hn).2
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
    have hlog : Real.log (sourceReactionCount n : ℝ) ≤
        Real.log (((n + 1) * 2 ^ (n + 1) : Nat) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by
          exact_mod_cast (lt_of_lt_of_le (pow_pos (by norm_num) n)
            (sourceReactionCount_bounds hn).1))
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact_mod_cast hb
    calc
      Real.log (sourceReactionCount n : ℝ) / (n : ℝ) ≤
          Real.log (((n + 1) * 2 ^ (n + 1) : Nat) : ℝ) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right hlog (by positivity)
      _ = upper n := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          Real.log_mul (by positivity : ((n + 1 : Nat) : ℝ) ≠ 0)
            (by positivity : ((2 : ℝ) ^ (n + 1)) ≠ 0),
          Real.log_pow]
        dsimp [upper]
        field_simp

theorem sourceReactionCount_tendsto_atTop :
    Tendsto sourceReactionCount atTop atTop := by
  have hp : Tendsto (fun n : Nat => 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hp
  filter_upwards [eventually_ge_atTop 4] with n hn
  exact (sourceReactionCount_bounds hn).1

theorem harmonic_sourceReactionCount_normalized :
    Tendsto (fun n : Nat =>
      (harmonic (sourceReactionCount n) : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  have herr : Tendsto (fun n : Nat =>
      (harmonic (sourceReactionCount n) : ℝ) -
        Real.log (sourceReactionCount n : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    convert Real.tendsto_harmonic_sub_log.comp sourceReactionCount_tendsto_atTop using 1
  have herrDiv := herr.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsum := herrDiv.add log_sourceReactionCount_normalized
  have hsum' : Tendsto (fun n : Nat =>
      ((harmonic (sourceReactionCount n) : ℝ) -
        Real.log (sourceReactionCount n : ℝ)) / (n : ℝ) +
          Real.log (sourceReactionCount n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
    simpa only [zero_add] using hsum
  apply hsum'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  ring

noncomputable def squareTail (R : Nat) : ℝ :=
  ∑' j : Nat, 1 / (((j + R : Nat) : ℝ) ^ 2)

theorem squareTail_le (R : Nat) (hR : 1 ≤ R) :
    squareTail R ≤ 2 / (R : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro n
  rw [Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun k : Nat => 1 / ((k : ℝ) ^ 2)) 0 n (c := R)]
  have h := sum_Ioo_inv_sq_le (α := ℝ) (R - 1) (R + n)
  have hset : Finset.Ioo (R - 1) (R + n) = Finset.Ico R (R + n) := by
    ext k
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  have hcast : (((R - 1 : Nat) : ℝ) + 1) = (R : ℝ) := by
    rw [Nat.cast_sub hR]
    norm_num
  rw [hset, hcast] at h
  simpa [Nat.add_comm, one_div] using h

theorem squareTail_nonneg (R : Nat) : 0 ≤ squareTail R := by
  exact tsum_nonneg (fun _ => by positivity)

theorem cappedSquareTail_le_two (R : Nat) (hR : 1 ≤ R) :
    (((R - 1 : Nat) : ℝ) * squareTail R) ≤ 2 := by
  calc
    (((R - 1 : Nat) : ℝ) * squareTail R) ≤
        ((R : Nat) : ℝ) * squareTail R := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.sub_le R 1
      · exact squareTail_nonneg R
    _ ≤ (R : ℝ) * (2 / (R : ℝ)) := by
      gcongr
      exact squareTail_le R hR
    _ = 2 := by
      have hR0 : (R : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hR))
      field_simp

noncomputable def squareInterior (R : Nat) : ℝ :=
  ∑ k ∈ Finset.Ico 2 R, 1 / ((k : ℝ) ^ 2)

noncomputable def criticalCappedNumerator (R : Nat) : ℝ :=
  (harmonic (R - 1) : ℝ) - 1 - squareInterior R +
    ((R - 1 : Nat) : ℝ) * squareTail R

theorem squareInterior_nonneg (R : Nat) : 0 ≤ squareInterior R := by
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem squareInterior_le_zetaTwo (R : Nat) :
    squareInterior R ≤ Real.pi ^ 2 / 6 := by
  dsimp [squareInterior]
  exact (hasSum_zeta_two.summable.sum_le_tsum (Finset.Ico 2 R)
    (fun _ _ => by positivity)).trans_eq hasSum_zeta_two.tsum_eq

theorem criticalCappedNumerator_bounds (R : Nat) (hR : 1 ≤ R) :
    (harmonic (R - 1) : ℝ) - (1 + Real.pi ^ 2 / 6) ≤
        criticalCappedNumerator R ∧
      criticalCappedNumerator R ≤ (harmonic (R - 1) : ℝ) + 1 := by
  constructor
  · dsimp [criticalCappedNumerator]
    have hi := squareInterior_le_zetaTwo R
    have ht := squareTail_nonneg R
    nlinarith
  · dsimp [criticalCappedNumerator]
    have hi := squareInterior_nonneg R
    have ht := cappedSquareTail_le_two R hR
    nlinarith

theorem sum_reciprocal_Ico_two (R : Nat) (hR : 2 ≤ R) :
    (∑ k ∈ Finset.Ico 2 R, 1 / (k : ℝ)) =
      (harmonic (R - 1) : ℝ) - 1 := by
  have hset : Finset.Icc 1 (R - 1) =
      insert 1 (Finset.Ico 2 R) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [harmonic_eq_sum_Icc, hset,
    Finset.sum_insert (by simp : 1 ∉ Finset.Ico 2 R)]
  simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  norm_num

noncomputable def directCriticalCappedNumerator (R : Nat) : ℝ :=
  (∑ k ∈ Finset.Ico 2 R,
      (((k - 1 : Nat) : ℝ) / ((k : ℝ) ^ 2))) +
    ((R - 1 : Nat) : ℝ) * squareTail R

theorem directCriticalCappedNumerator_eq (R : Nat) (hR : 2 ≤ R) :
    directCriticalCappedNumerator R = criticalCappedNumerator R := by
  have hterm : ∀ k ∈ Finset.Ico 2 R,
      (((k - 1 : Nat) : ℝ) / ((k : ℝ) ^ 2)) =
        1 / (k : ℝ) - 1 / ((k : ℝ) ^ 2) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk1 : 1 ≤ k := by omega
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < k))
    rw [Nat.cast_sub hk1]
    field_simp
    ring
  dsimp [directCriticalCappedNumerator, criticalCappedNumerator, squareInterior]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    sum_reciprocal_Ico_two R hR]

theorem harmonic_pred_bounds (R : Nat) (hR : 1 ≤ R) :
    (harmonic R : ℝ) - 1 ≤ (harmonic (R - 1) : ℝ) ∧
      (harmonic (R - 1) : ℝ) ≤ (harmonic R : ℝ) := by
  have hs := congr_arg ((↑) : ℚ → ℝ) (harmonic_succ (R - 1))
  rw [Nat.sub_add_cancel hR] at hs
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at hs
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hinv0 : 0 ≤ ((R : ℝ)⁻¹) := by positivity
  have hinv1 : ((R : ℝ)⁻¹) ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 hRreal
  constructor <;> nlinarith

theorem harmonic_sourceReactionCount_pred_normalized :
    Tendsto (fun n : Nat =>
      (harmonic (sourceReactionCount n - 1) : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  have honeDiv : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun n : Nat =>
      (harmonic (sourceReactionCount n) : ℝ) / (n : ℝ) -
        1 / (n : ℝ)) atTop (𝓝 (Real.log 2)) := by
    simpa only [sub_zero] using
      harmonic_sourceReactionCount_normalized.sub honeDiv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl
    harmonic_sourceReactionCount_normalized
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hR : 1 ≤ sourceReactionCount n := by
      have hp : 0 < 2 ^ n := pow_pos (by omega) n
      exact (by omega : 1 ≤ 2 ^ n).trans (sourceReactionCount_bounds hn).1
    have hp := (harmonic_pred_bounds (sourceReactionCount n) hR).1
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
    calc
      (harmonic (sourceReactionCount n) : ℝ) / (n : ℝ) - 1 / (n : ℝ) =
          ((harmonic (sourceReactionCount n) : ℝ) - 1) / (n : ℝ) := by
            field_simp
      _ ≤ (harmonic (sourceReactionCount n - 1) : ℝ) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right hp (by positivity)
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hR : 1 ≤ sourceReactionCount n := by
      have hp : 0 < 2 ^ n := pow_pos (by omega) n
      exact (by omega : 1 ≤ 2 ^ n).trans (sourceReactionCount_bounds hn).1
    have hp := (harmonic_pred_bounds (sourceReactionCount n) hR).2
    exact div_le_div_of_nonneg_right hp (by positivity)

theorem criticalCappedNumerator_source_normalized :
    Tendsto (fun n : Nat =>
      criticalCappedNumerator (sourceReactionCount n) / (n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  let C : ℝ := 1 + Real.pi ^ 2 / 6
  have hCDiv : Tendsto (fun n : Nat => C / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have honeDiv : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun n : Nat =>
      (harmonic (sourceReactionCount n - 1) : ℝ) / (n : ℝ) -
        C / (n : ℝ)) atTop (𝓝 (Real.log 2)) := by
    simpa only [sub_zero] using
      harmonic_sourceReactionCount_pred_normalized.sub hCDiv
  have hu : Tendsto (fun n : Nat =>
      (harmonic (sourceReactionCount n - 1) : ℝ) / (n : ℝ) +
        1 / (n : ℝ)) atTop (𝓝 (Real.log 2)) := by
    simpa only [add_zero] using
      harmonic_sourceReactionCount_pred_normalized.add honeDiv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hR : 1 ≤ sourceReactionCount n := by
      have hp : 0 < 2 ^ n := pow_pos (by omega) n
      exact (by omega : 1 ≤ 2 ^ n).trans (sourceReactionCount_bounds hn).1
    have hb := (criticalCappedNumerator_bounds (sourceReactionCount n) hR).1
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
    calc
      (harmonic (sourceReactionCount n - 1) : ℝ) / (n : ℝ) - C / (n : ℝ) =
          ((harmonic (sourceReactionCount n - 1) : ℝ) - C) / (n : ℝ) := by
            field_simp
      _ ≤ criticalCappedNumerator (sourceReactionCount n) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right (by simpa [C] using hb) (by positivity)
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hR : 1 ≤ sourceReactionCount n := by
      have hp : 0 < 2 ^ n := pow_pos (by omega) n
      exact (by omega : 1 ≤ 2 ^ n).trans (sourceReactionCount_bounds hn).1
    have hb := (criticalCappedNumerator_bounds (sourceReactionCount n) hR).2
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
    calc
      criticalCappedNumerator (sourceReactionCount n) / (n : ℝ) ≤
          ((harmonic (sourceReactionCount n - 1) : ℝ) + 1) / (n : ℝ) := by
            exact div_le_div_of_nonneg_right hb (by positivity)
      _ = (harmonic (sourceReactionCount n - 1) : ℝ) / (n : ℝ) +
          1 / (n : ℝ) := by field_simp

theorem directCriticalCappedNumerator_source_normalized :
    Tendsto (fun n : Nat =>
      directCriticalCappedNumerator (sourceReactionCount n) / (n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  apply criticalCappedNumerator_source_normalized.congr'
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hR : 2 ≤ sourceReactionCount n := by
    have hpow : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hpow
    exact hpow.trans (sourceReactionCount_bounds hn).1
  rw [directCriticalCappedNumerator_eq (sourceReactionCount n) hR]

noncomputable def criticalZipfTwoMean (R : Nat) : ℝ :=
  directCriticalCappedNumerator R / (Real.pi ^ 2 / 6)

theorem criticalZipfTwoMean_source_normalized :
    Tendsto (fun n : Nat =>
      criticalZipfTwoMean (sourceReactionCount n) / (n : ℝ))
      atTop (𝓝 (Real.log 2 / (Real.pi ^ 2 / 6))) := by
  have h := directCriticalCappedNumerator_source_normalized.div_const
    (Real.pi ^ 2 / 6)
  convert h using 1
  · funext n
    dsimp [criticalZipfTwoMean]
    ring

theorem sourceReactionCount_rpow_window (b : ℝ) :
    Tendsto (fun n : Nat =>
      (sourceReactionCount n : ℝ) ^ (-b / (n : ℝ)))
      atTop (𝓝 ((2 : ℝ) ^ (-b))) := by
  have hc : Tendsto (fun _ : Nat => -b) atTop (𝓝 (-b)) :=
    tendsto_const_nhds
  have hmul := hc.mul log_sourceReactionCount_normalized
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hmul
  convert hexp using 1
  · funext n
    have hsrc : 0 < (sourceReactionCount n : ℝ) := by
      rw [sourceReactionCount]
      positivity
    rw [Real.rpow_def_of_pos hsrc]
    dsimp only [Function.comp_apply]
    congr 1
    ring
  · rw [Real.rpow_def_of_pos (by positivity)]
    rw [mul_comm]

theorem sourceWindowIntegral_normalized (b : ℝ) :
    Tendsto (fun n : Nat =>
      (1 - (sourceReactionCount n : ℝ) ^ (-b / (n : ℝ))) / b)
      atTop (𝓝 ((1 - (2 : ℝ) ^ (-b)) / b)) := by
  exact ((tendsto_const_nhds.sub (sourceReactionCount_rpow_window b)).div_const b)

noncomputable def tiltedHarmonic (p : ℝ) (R : Nat) : ℝ :=
  ∑ k ∈ Finset.Ico 1 R, (k : ℝ) ^ (-p)

theorem tiltedHarmonic_integral_bounds (p : ℝ) (hp : 0 < p)
    (R : Nat) (hR : 2 ≤ R) :
    (∫ x in (1 : ℝ)..(R : ℝ), x ^ (-p)) ≤ tiltedHarmonic p R ∧
      tiltedHarmonic p R ≤
        1 + ∫ x in (1 : ℝ)..(R : ℝ), x ^ (-p) := by
  have hf : AntitoneOn (fun x : ℝ => x ^ (-p))
      (Set.Icc ((1 : Nat) : ℝ) ((R : Nat) : ℝ)) := by
    apply (Real.strictAntiOn_rpow_Ioi_of_exponent_neg (by linarith)).antitoneOn.mono
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by simpa only [Nat.cast_one] using hx.1
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one hx1)
  constructor
  · dsimp [tiltedHarmonic]
    simpa only [Nat.cast_one] using
      (AntitoneOn.integral_le_sum_Ico
        (f := fun x : ℝ => x ^ (-p)) (a := 1) (b := R)
        (by omega : 1 ≤ R) hf)
  · have hu := AntitoneOn.sum_le_integral_Ico
      (f := fun x : ℝ => x ^ (-p)) (a := 1) (b := R)
      (by omega : 1 ≤ R) hf
    rw [Finset.sum_Ico_add'
      (fun k : Nat => (k : ℝ) ^ (-p)) 1 R (c := 1)] at hu
    have htail :
        (∑ k ∈ Finset.Ico 2 R, (k : ℝ) ^ (-p)) ≤
          ∑ k ∈ Finset.Ico 2 (R + 1), (k : ℝ) ^ (-p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [Finset.mem_Ico] at hk ⊢
        omega
      · intro k _ _
        positivity
    calc
      tiltedHarmonic p R =
          1 + ∑ k ∈ Finset.Ico 2 R, (k : ℝ) ^ (-p) := by
            dsimp [tiltedHarmonic]
            rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < R)]
            norm_num
      _ ≤ 1 + ∑ k ∈ Finset.Ico 2 (R + 1), (k : ℝ) ^ (-p) :=
        add_le_add_right htail 1
      _ ≤ 1 + ∫ x in (1 : ℝ)..(R : ℝ), x ^ (-p) :=
        by simpa only [Nat.cast_one, Nat.reduceAdd] using add_le_add_right hu 1

theorem sourceWindowIntegral_eq (b : ℝ) (hb : b ≠ 0)
    (n : Nat) (hn : 1 ≤ n) :
    (∫ x in (1 : ℝ)..(sourceReactionCount n : ℝ),
        x ^ (-(1 + b / (n : ℝ)))) / (n : ℝ) =
      (1 - (sourceReactionCount n : ℝ) ^ (-b / (n : ℝ))) / b := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsrc : (1 : ℝ) ≤ (sourceReactionCount n : ℝ) := by
    have hnat : 1 ≤ sourceReactionCount n := by
      rw [sourceReactionCount]
      omega
    exact_mod_cast hnat
  have hr : -(1 + b / (n : ℝ)) ≠ -1 := by
    intro h
    have hd : b / (n : ℝ) = 0 := by linarith
    exact hb ((div_eq_zero_iff.mp hd).resolve_right hn0)
  have hzero : (0 : ℝ) ∉
      Set.uIcc (1 : ℝ) (sourceReactionCount n : ℝ) := by
    rw [Set.uIcc_of_le hsrc]
    simp
  rw [integral_rpow (Or.inr ⟨hr, hzero⟩)]
  rw [Real.one_rpow]
  have hexp : -(1 + b / (n : ℝ)) + 1 = -b / (n : ℝ) := by ring
  rw [hexp]
  field_simp [hb, hn0]
  ring

theorem tiltedHarmonic_source_window_normalized (b : ℝ) (hb : b ≠ 0) :
    Tendsto (fun n : Nat =>
      tiltedHarmonic (1 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ))
      atTop (𝓝 ((1 - (2 : ℝ) ^ (-b)) / b)) := by
  have hI : Tendsto (fun n : Nat =>
      (∫ x in (1 : ℝ)..(sourceReactionCount n : ℝ),
        x ^ (-(1 + b / (n : ℝ)))) / (n : ℝ))
      atTop (𝓝 ((1 - (2 : ℝ) ^ (-b)) / b)) := by
    apply (sourceWindowIntegral_normalized b).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (sourceWindowIntegral_eq b hb n hn).symm
  have honeDiv : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hu : Tendsto (fun n : Nat =>
      (∫ x in (1 : ℝ)..(sourceReactionCount n : ℝ),
        x ^ (-(1 + b / (n : ℝ)))) / (n : ℝ) + 1 / (n : ℝ))
      atTop (𝓝 ((1 - (2 : ℝ) ^ (-b)) / b)) := by
    simpa only [add_zero] using hI.add honeDiv
  have hbn : Tendsto (fun n : Nat => b / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpT : Tendsto (fun n : Nat => 1 + b / (n : ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).add hbn
  have hpEv : ∀ᶠ n : Nat in atTop, 0 < 1 + b / (n : ℝ) :=
    hpT (Ioi_mem_nhds zero_lt_one)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hI hu
  · filter_upwards [eventually_ge_atTop 4, hpEv] with n hn hp
    have hR : 2 ≤ sourceReactionCount n := by
      have hpow : 2 ^ 1 ≤ 2 ^ n :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      exact hpow.trans (sourceReactionCount_bounds hn).1
    have hbound := (tiltedHarmonic_integral_bounds
      (1 + b / (n : ℝ)) hp (sourceReactionCount n) hR).1
    exact div_le_div_of_nonneg_right hbound (by positivity)
  · filter_upwards [eventually_ge_atTop 4, hpEv] with n hn hp
    have hR : 2 ≤ sourceReactionCount n := by
      have hpow : 2 ^ 1 ≤ 2 ^ n :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      exact hpow.trans (sourceReactionCount_bounds hn).1
    have hbound := (tiltedHarmonic_integral_bounds
      (1 + b / (n : ℝ)) hp (sourceReactionCount n) hR).2
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
    calc
      tiltedHarmonic (1 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ) ≤
          (1 + ∫ x in (1 : ℝ)..(sourceReactionCount n : ℝ),
            x ^ (-(1 + b / (n : ℝ)))) / (n : ℝ) := by
              exact div_le_div_of_nonneg_right hbound (by positivity)
      _ = (∫ x in (1 : ℝ)..(sourceReactionCount n : ℝ),
            x ^ (-(1 + b / (n : ℝ)))) / (n : ℝ) + 1 / (n : ℝ) := by
              field_simp
              ring

noncomputable def zipfNormalizer (a : ℝ) : ℝ :=
  ∑' k : Nat, (k : ℝ) ^ (-a)

theorem zipfNormalizer_two :
    zipfNormalizer 2 = Real.pi ^ 2 / 6 := by
  dsimp [zipfNormalizer]
  calc
    (∑' k : Nat, (k : ℝ) ^ (-(2 : ℝ))) =
        ∑' k : Nat, 1 / ((k : ℝ) ^ 2) := by
      apply tsum_congr
      intro k
      rw [Real.rpow_neg (Nat.cast_nonneg k)]
      simp only [one_div]
      congr 1
      exact Real.rpow_natCast (k : ℝ) 2
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq

theorem zipfNormalizer_source_window (b : ℝ) :
    Tendsto (fun n : Nat => zipfNormalizer (2 + b / (n : ℝ)))
      atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have hbn : Tendsto (fun n : Nat => b / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have ha : Tendsto (fun n : Nat => 2 + b / (n : ℝ)) atTop (𝓝 2) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : ℝ)) atTop (𝓝 2)).add hbn
  have hneg : Tendsto (fun n : Nat => -(2 + b / (n : ℝ))) atTop (𝓝 (-2)) :=
    ha.neg
  let bound : Nat → ℝ := fun k => (k : ℝ) ^ (-(3 / 2 : ℝ))
  have hsum : Summable bound := by
    dsimp [bound]
    exact Real.summable_nat_rpow.mpr (by norm_num)
  have hab : ∀ k : Nat, Tendsto
      (fun n : Nat => (k : ℝ) ^ (-(2 + b / (n : ℝ))))
      atTop (𝓝 ((k : ℝ) ^ (-(2 : ℝ)))) := by
    intro k
    by_cases hk : k = 0
    · subst k
      norm_num only [Nat.cast_zero]
      have hev : ∀ᶠ n : Nat in atTop, -(2 + b / (n : ℝ)) < 0 :=
        hneg (Iio_mem_nhds (by norm_num : (-2 : ℝ) < 0))
      refine (tendsto_congr' ?_).2
        (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
      filter_upwards [hev] with n hn
      rw [Real.zero_rpow (ne_of_lt hn)]
    · exact (Real.continuous_const_rpow (by exact_mod_cast hk)).continuousAt.tendsto.comp hneg
  have haEv : ∀ᶠ n : Nat in atTop, (3 / 2 : ℝ) < 2 + b / (n : ℝ) :=
    ha (Ioi_mem_nhds (by norm_num : (3 / 2 : ℝ) < 2))
  have hbound : ∀ᶠ n : Nat in atTop, ∀ k : Nat,
      ‖(k : ℝ) ^ (-(2 + b / (n : ℝ)))‖ ≤ bound k := by
    filter_upwards [haEv] with n hn k
    by_cases hk : k = 0
    · subst k
      norm_num only [Nat.cast_zero]
      have hnegexp : -(2 + b / (n : ℝ)) < 0 := by linarith
      dsimp [bound]
      rw [Real.zero_rpow (ne_of_lt hnegexp)]
      norm_num
    · rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)]
      dsimp [bound]
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
      · linarith
  have ht := tendsto_tsum_of_dominated_convergence hsum hab hbound
  change Tendsto (fun n : Nat => zipfNormalizer (2 + b / (n : ℝ)))
    atTop (𝓝 (zipfNormalizer 2)) at ht
  simpa only [zipfNormalizer_two] using ht

theorem rpow_sum_Ico_le_integral (a : ℝ) (ha : 0 < a)
    (A B : Nat) (hA : 1 ≤ A) (hAB : A < B) :
    (∑ k ∈ Finset.Ico A B, (k : ℝ) ^ (-a)) ≤
      (A : ℝ) ^ (-a) + ∫ x in (A : ℝ)..(B : ℝ), x ^ (-a) := by
  have hf : AntitoneOn (fun x : ℝ => x ^ (-a))
      (Set.Icc ((A : Nat) : ℝ) ((B : Nat) : ℝ)) := by
    apply (Real.strictAntiOn_rpow_Ioi_of_exponent_neg (by linarith)).antitoneOn.mono
    intro x hx
    have hxA : (A : ℝ) ≤ x := hx.1
    have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
    exact Set.mem_Ioi.mpr (hApos.trans_le hxA)
  have hu := AntitoneOn.sum_le_integral_Ico
    (f := fun x : ℝ => x ^ (-a)) (a := A) (b := B)
    hAB.le hf
  rw [Finset.sum_Ico_add'
    (fun k : Nat => (k : ℝ) ^ (-a)) A B (c := 1)] at hu
  have htail :
      (∑ k ∈ Finset.Ico (A + 1) B, (k : ℝ) ^ (-a)) ≤
        ∑ k ∈ Finset.Ico (A + 1) (B + 1), (k : ℝ) ^ (-a) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro k _ _
      positivity
  calc
    (∑ k ∈ Finset.Ico A B, (k : ℝ) ^ (-a)) =
        (A : ℝ) ^ (-a) +
          ∑ k ∈ Finset.Ico (A + 1) B, (k : ℝ) ^ (-a) := by
            rw [Finset.sum_eq_sum_Ico_succ_bot hAB]
    _ ≤ (A : ℝ) ^ (-a) +
        ∑ k ∈ Finset.Ico (A + 1) (B + 1), (k : ℝ) ^ (-a) :=
      add_le_add_right htail _
    _ ≤ (A : ℝ) ^ (-a) +
        ∫ x in (A : ℝ)..(B : ℝ), x ^ (-a) :=
      add_le_add_right hu _

noncomputable def rpowTail (a : ℝ) (R : Nat) : ℝ :=
  ∑' j : Nat, ((j + R : Nat) : ℝ) ^ (-a)

theorem rpowTail_le (a : ℝ) (ha : 1 < a) (R : Nat) (hR : 1 ≤ R) :
    rpowTail a R ≤
      (R : ℝ) ^ (-a) + (R : ℝ) ^ (1 - a) / (a - 1) := by
  apply Real.tsum_le_of_sum_range_le (fun _ => Real.rpow_nonneg (by positivity) _)
  intro m
  cases m with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ m =>
      rw [Finset.range_eq_Ico,
        Finset.sum_Ico_add' (fun k : Nat => (k : ℝ) ^ (-a))
          0 (m + 1) (c := R)]
      simp only [Nat.zero_add]
      have hs := rpow_sum_Ico_le_integral a (by linarith) R ((m + 1) + R) hR (by omega)
      refine hs.trans (add_le_add_right ?_ ((R : ℝ) ^ (-a)))
      have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      have hBreal : (R : ℝ) ≤ (((m + 1) + R : Nat) : ℝ) := by
        exact_mod_cast Nat.le_add_left R (m + 1)
      have hr : -a ≠ -1 := by linarith
      have hzero : (0 : ℝ) ∉ Set.uIcc (R : ℝ) ((m + 1) + R : Nat) := by
        rw [Set.uIcc_of_le hBreal]
        simp only [Set.mem_Icc, not_and_or, not_le]
        exact Or.inl (lt_of_lt_of_le zero_lt_one hRreal)
      rw [integral_rpow (Or.inr ⟨hr, hzero⟩)]
      have hden : 0 < a - 1 := sub_pos.mpr ha
      have heq :
          ((((m + 1) + R : Nat) : ℝ) ^ (-a + 1) -
              (R : ℝ) ^ (-a + 1)) / (-a + 1) =
            ((R : ℝ) ^ (1 - a) -
              (((m + 1) + R : Nat) : ℝ) ^ (1 - a)) / (a - 1) := by
        have hden0 : a - 1 ≠ 0 := ne_of_gt hden
        have hden1 : 1 - a ≠ 0 := by linarith
        rw [show -a + 1 = 1 - a by ring]
        field_simp [hden0, hden1]
        ring
      rw [heq]
      exact div_le_div_of_nonneg_right
        (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) hden.le

theorem rpowTail_nonneg (a : ℝ) (R : Nat) : 0 ≤ rpowTail a R := by
  exact tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)

noncomputable def cappedRpowTail (a : ℝ) (R : Nat) : ℝ :=
  (((R - 1 : Nat) : ℝ) * rpowTail a R)

theorem cappedRpowTail_nonneg (a : ℝ) (R : Nat) :
    0 ≤ cappedRpowTail a R := by
  exact mul_nonneg (by positivity) (rpowTail_nonneg a R)

theorem cappedRpowTail_le (a : ℝ) (ha : 1 < a)
    (R : Nat) (hR : 1 ≤ R) :
    cappedRpowTail a R ≤
      (R : ℝ) ^ (1 - a) + (R : ℝ) ^ (2 - a) / (a - 1) := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hmul1 : (R : ℝ) * (R : ℝ) ^ (-a) = (R : ℝ) ^ (1 - a) := by
    calc
      (R : ℝ) * (R : ℝ) ^ (-a) = (R : ℝ) ^ (1 : ℝ) * (R : ℝ) ^ (-a) := by
        rw [Real.rpow_one]
      _ = (R : ℝ) ^ ((1 : ℝ) + (-a)) := (Real.rpow_add hRpos 1 (-a)).symm
      _ = (R : ℝ) ^ (1 - a) := by ring_nf
  have hmul2 : (R : ℝ) * (R : ℝ) ^ (1 - a) = (R : ℝ) ^ (2 - a) := by
    calc
      (R : ℝ) * (R : ℝ) ^ (1 - a) =
          (R : ℝ) ^ (1 : ℝ) * (R : ℝ) ^ (1 - a) := by rw [Real.rpow_one]
      _ = (R : ℝ) ^ ((1 : ℝ) + (1 - a)) :=
        (Real.rpow_add hRpos 1 (1 - a)).symm
      _ = (R : ℝ) ^ (2 - a) := by ring_nf
  calc
    cappedRpowTail a R ≤ (R : ℝ) * rpowTail a R := by
      dsimp [cappedRpowTail]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.sub_le R 1
      · exact rpowTail_nonneg a R
    _ ≤ (R : ℝ) *
        ((R : ℝ) ^ (-a) + (R : ℝ) ^ (1 - a) / (a - 1)) := by
      exact mul_le_mul_of_nonneg_left (rpowTail_le a ha R hR) hRpos.le
    _ = (R : ℝ) ^ (1 - a) + (R : ℝ) ^ (2 - a) / (a - 1) := by
      rw [mul_add, hmul1, ← mul_div_assoc, hmul2]

theorem sourceReactionCount_inv_tendsto_zero :
    Tendsto (fun n : Nat => (sourceReactionCount n : ℝ)⁻¹)
      atTop (𝓝 0) := by
  have hreal : Tendsto (fun n : Nat => (sourceReactionCount n : ℝ))
      atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceReactionCount_tendsto_atTop
  exact hreal.inv_tendsto_atTop

theorem cappedRpowTail_source_window_normalized (b : ℝ) :
    Tendsto (fun n : Nat =>
      cappedRpowTail (2 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ))
      atTop (𝓝 0) := by
  have hr := sourceReactionCount_rpow_window b
  have hfirst0 : Tendsto (fun n : Nat =>
      (sourceReactionCount n : ℝ) ^ (1 - (2 + b / (n : ℝ))))
      atTop (𝓝 0) := by
    have hp := sourceReactionCount_inv_tendsto_zero.mul hr
    have hp0 : Tendsto (fun n : Nat =>
        (sourceReactionCount n : ℝ)⁻¹ *
          (sourceReactionCount n : ℝ) ^ (-b / (n : ℝ)))
        atTop (𝓝 0) := by
      simpa only [zero_mul] using hp
    apply hp0.congr'
    filter_upwards with n
    have hsrc : 0 < (sourceReactionCount n : ℝ) := by
      rw [sourceReactionCount]
      positivity
    rw [show 1 - (2 + b / (n : ℝ)) = (-1 : ℝ) + (-b / (n : ℝ)) by ring,
      Real.rpow_add hsrc, Real.rpow_neg_one]
  have hsecond : Tendsto (fun n : Nat =>
      (sourceReactionCount n : ℝ) ^ (2 - (2 + b / (n : ℝ))))
      atTop (𝓝 ((2 : ℝ) ^ (-b))) := by
    apply hr.congr'
    filter_upwards with n
    congr 1
    ring
  have hbn : Tendsto (fun n : Nat => b / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hden : Tendsto (fun n : Nat => (2 + b / (n : ℝ)) - 1)
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : ℝ)) atTop (𝓝 2)).add hbn
    have hone : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    convert h.sub hone using 1
    norm_num [sub_eq_add_neg]
  have hsecondDiv := hsecond.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hupper : Tendsto (fun n : Nat =>
      (sourceReactionCount n : ℝ) ^ (1 - (2 + b / (n : ℝ))) +
        (sourceReactionCount n : ℝ) ^ (2 - (2 + b / (n : ℝ))) /
          ((2 + b / (n : ℝ)) - 1))
      atTop (𝓝 ((2 : ℝ) ^ (-b))) := by
    simpa only [Pi.div_apply, div_one, zero_add] using hfirst0.add hsecondDiv
  have hupperDiv := hupper.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0)) hupperDiv
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (cappedRpowTail_nonneg _ _) (by positivity)
  · have haT : Tendsto (fun n : Nat => 2 + b / (n : ℝ)) atTop (𝓝 2) := by
      simpa only [add_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : ℝ)) atTop (𝓝 2)).add hbn
    have haEv : ∀ᶠ n : Nat in atTop, 1 < 2 + b / (n : ℝ) :=
      haT (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))
    filter_upwards [eventually_ge_atTop 4, haEv] with n hn ha
    have hR : 1 ≤ sourceReactionCount n := by
      have hp : 0 < 2 ^ n := pow_pos (by omega) n
      exact (by omega : 1 ≤ 2 ^ n).trans (sourceReactionCount_bounds hn).1
    exact div_le_div_of_nonneg_right
      (cappedRpowTail_le (2 + b / (n : ℝ)) ha (sourceReactionCount n) hR)
      (by positivity)

noncomputable def windowDirectNumerator (a : ℝ) (R : Nat) : ℝ :=
  (∑ k ∈ Finset.Ico 2 R,
      (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a))) +
    cappedRpowTail a R

theorem windowDirectNumerator_eq (a : ℝ) (R : Nat) (hR : 2 ≤ R) :
    windowDirectNumerator a R =
      tiltedHarmonic (a - 1) R - 1 -
        (∑ k ∈ Finset.Ico 2 R, (k : ℝ) ^ (-a)) +
          cappedRpowTail a R := by
  have hterm : ∀ k ∈ Finset.Ico 2 R,
      (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a)) =
        (k : ℝ) ^ (-(a - 1)) - (k : ℝ) ^ (-a) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk1 : 1 ≤ k := by omega
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hmul : (k : ℝ) * (k : ℝ) ^ (-a) =
        (k : ℝ) ^ (-(a - 1)) := by
      calc
        (k : ℝ) * (k : ℝ) ^ (-a) =
            (k : ℝ) ^ (1 : ℝ) * (k : ℝ) ^ (-a) := by rw [Real.rpow_one]
        _ = (k : ℝ) ^ ((1 : ℝ) + (-a)) :=
          (Real.rpow_add hkpos 1 (-a)).symm
        _ = (k : ℝ) ^ (-(a - 1)) := by ring_nf
    rw [Nat.cast_sub hk1]
    rw [sub_mul]
    norm_num only [Nat.cast_one, one_mul]
    rw [hmul]
  have htilt :
      (∑ k ∈ Finset.Ico 2 R, (k : ℝ) ^ (-(a - 1))) =
        tiltedHarmonic (a - 1) R - 1 := by
    have hs : tiltedHarmonic (a - 1) R =
        1 + ∑ k ∈ Finset.Ico 2 R, (k : ℝ) ^ (-(a - 1)) := by
      dsimp [tiltedHarmonic]
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < R)]
      norm_num
    linarith
  dsimp [windowDirectNumerator]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, htilt]

theorem windowInterior_nonneg (a : ℝ) (R : Nat) :
    0 ≤ ∑ k ∈ Finset.Ico 2 R, (k : ℝ) ^ (-a) := by
  exact Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (by positivity) _)

theorem windowInterior_le_normalizer (a : ℝ) (ha : 1 < a) (R : Nat) :
    (∑ k ∈ Finset.Ico 2 R, (k : ℝ) ^ (-a)) ≤ zipfNormalizer a := by
  dsimp [zipfNormalizer]
  exact (Real.summable_nat_rpow.mpr (by linarith : -a < -1)).sum_le_tsum (Finset.Ico 2 R)
    (fun _ _ => Real.rpow_nonneg (by positivity) _)

theorem windowInterior_source_window_normalized (b : ℝ) :
    Tendsto (fun n : Nat =>
      (∑ k ∈ Finset.Ico 2 (sourceReactionCount n),
        (k : ℝ) ^ (-(2 + b / (n : ℝ)))) / (n : ℝ))
      atTop (𝓝 0) := by
  have hupper := (zipfNormalizer_source_window b).div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbn : Tendsto (fun n : Nat => b / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have haT : Tendsto (fun n : Nat => 2 + b / (n : ℝ)) atTop (𝓝 2) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : ℝ)) atTop (𝓝 2)).add hbn
  have haEv : ∀ᶠ n : Nat in atTop, 1 < 2 + b / (n : ℝ) :=
    haT (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0)) hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (windowInterior_nonneg _ _) (by positivity)
  · filter_upwards [eventually_ge_atTop 1, haEv] with n hn ha
    exact div_le_div_of_nonneg_right
      (windowInterior_le_normalizer (2 + b / (n : ℝ)) ha
        (sourceReactionCount n)) (by positivity)

theorem windowDirectNumerator_source_window_normalized (b : ℝ) (hb : b ≠ 0) :
    Tendsto (fun n : Nat =>
      windowDirectNumerator (2 + b / (n : ℝ)) (sourceReactionCount n) /
        (n : ℝ))
      atTop (𝓝 ((1 - (2 : ℝ) ^ (-b)) / b)) := by
  have htilt := tiltedHarmonic_source_window_normalized b hb
  have hone : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinterior := windowInterior_source_window_normalized b
  have hcap := cappedRpowTail_source_window_normalized b
  have hcombined := ((htilt.sub hone).sub hinterior).add hcap
  have hlimit : Tendsto (fun n : Nat =>
      tiltedHarmonic (1 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ) -
        1 / (n : ℝ) -
        (∑ k ∈ Finset.Ico 2 (sourceReactionCount n),
          (k : ℝ) ^ (-(2 + b / (n : ℝ)))) / (n : ℝ) +
        cappedRpowTail (2 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ))
      atTop (𝓝 ((1 - (2 : ℝ) ^ (-b)) / b)) := by
    simpa only [sub_zero, add_zero] using hcombined
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hR : 2 ≤ sourceReactionCount n := by
    have hpow : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hpow
    exact hpow.trans (sourceReactionCount_bounds hn).1
  rw [windowDirectNumerator_eq (2 + b / (n : ℝ))
    (sourceReactionCount n) hR]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  field_simp
  ring_nf

noncomputable def windowZipfMean (a : ℝ) (R : Nat) : ℝ :=
  windowDirectNumerator a R / zipfNormalizer a

theorem windowZipfMean_source_window_normalized_of_ne_zero
    (b : ℝ) (hb : b ≠ 0) :
    Tendsto (fun n : Nat =>
      windowZipfMean (2 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ))
      atTop (𝓝 (((1 - (2 : ℝ) ^ (-b)) / b) / (Real.pi ^ 2 / 6))) := by
  have hnum := windowDirectNumerator_source_window_normalized b hb
  have hden := zipfNormalizer_source_window b
  have hzeta : Real.pi ^ 2 / 6 ≠ 0 := by positivity
  have hquot := hnum.div hden hzeta
  convert hquot using 1
  funext n
  dsimp [windowZipfMean]
  ring

theorem criticalLambda_of_ne_zero (b : ℝ) (hb : b ≠ 0) :
    criticalLambda b =
      ((1 - (2 : ℝ) ^ (-b)) / b) / (Real.pi ^ 2 / 6) := by
  rw [criticalLambda, if_neg hb, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2)]
  have hzeta : Real.pi ^ 2 / 6 ≠ 0 := by positivity
  field_simp [hb, hzeta]

theorem rpowTail_two_eq_squareTail (R : Nat) :
    rpowTail 2 R = squareTail R := by
  dsimp [rpowTail, squareTail]
  apply tsum_congr
  intro j
  rw [Real.rpow_neg (by positivity)]
  simp only [one_div]
  congr 1
  exact Real.rpow_natCast (((j + R : Nat) : ℝ)) 2

theorem windowDirectNumerator_two_eq (R : Nat) :
    windowDirectNumerator 2 R = directCriticalCappedNumerator R := by
  have hterm : ∀ k ∈ Finset.Ico 2 R,
      (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-(2 : ℝ))) =
        ((k - 1 : Nat) : ℝ) / ((k : ℝ) ^ 2) := by
    intro k hk
    rw [Real.rpow_neg (by positivity)]
    rw [div_eq_mul_inv]
    congr 2
    exact Real.rpow_natCast (k : ℝ) 2
  dsimp [windowDirectNumerator, directCriticalCappedNumerator, cappedRpowTail]
  rw [Finset.sum_congr rfl hterm, rpowTail_two_eq_squareTail]

theorem windowZipfMean_two_eq (R : Nat) :
    windowZipfMean 2 R = criticalZipfTwoMean R := by
  dsimp [windowZipfMean, criticalZipfTwoMean]
  rw [windowDirectNumerator_two_eq, zipfNormalizer_two]

theorem windowZipfMean_two_source_normalized :
    Tendsto (fun n : Nat =>
      windowZipfMean 2 (sourceReactionCount n) / (n : ℝ))
      atTop (𝓝 (criticalLambda 0)) := by
  rw [criticalLambda_zero]
  apply criticalZipfTwoMean_source_normalized.congr'
  filter_upwards with n
  rw [windowZipfMean_two_eq]

theorem windowZipfMean_source_window_normalized (b : ℝ) :
    Tendsto (fun n : Nat =>
      windowZipfMean (2 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ))
      atTop (𝓝 (criticalLambda b)) := by
  by_cases hb : b = 0
  · subst b
    simpa using windowZipfMean_two_source_normalized
  · rw [criticalLambda_of_ne_zero b hb]
    exact windowZipfMean_source_window_normalized_of_ne_zero b hb


end PowerLawSmallRAF
