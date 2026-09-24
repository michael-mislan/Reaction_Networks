import proofs.OverlapCorrectedRAF.Asymptotic.SublinearCatalysis
import proofs.RAF.Asymptotics.FixedGap

namespace OverlapCorrectedRAF.Asymptotic

open Filter Topology
open RAF.Polymer
open OverlapCorrectedRAF.Source

theorem repositoryGatewayCoordinateCount_tendsto :
    Tendsto repositoryGatewayCoordinateCount atTop atTop := by
  have hpow : Tendsto (fun n : Nat => 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Nat) < 2)
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [repositoryGatewayCoordinateCount_exact, pow_succ]
  have hp : 1 < 2 ^ n :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  omega

/-- At the first nontrivial scale `f_n = lambda*n`, the expected number of
open coordinates in the 34-channel repository gateway remains uniformly
bounded. -/
theorem repository_linear_rate_mul_gatewayCoordinateCount_le
    {lambda : ℝ} (hlambda : 0 ≤ lambda) {n : Nat} (hn : 3 ≤ n) :
    repositoryCatalysisP (lambda * n) n * repositoryGatewayCoordinateCount n ≤
      272 * lambda := by
  let X : ℝ := (2 ^ (n + 1) - 2 : Nat)
  let J : ℝ := Fintype.card (RepositoryChannel n)
  let m : ℝ := ((n - 1) / 2 : Nat)
  let P : ℝ := (2 ^ n : Nat)
  have hmNat : 0 < (n - 1) / 2 := by omega
  have hJnat := repositoryChannel_card_lower hn
  have hJposNat : 0 < Fintype.card (RepositoryChannel n) :=
    lt_of_lt_of_le (Nat.mul_pos hmNat (pow_pos (by norm_num) _)) hJnat
  have hJpos : 0 < J := by
    dsimp [J]
    exact_mod_cast hJposNat
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hJlower : m * P ≤ J := by
    dsimp [m, P, J]
    exact_mod_cast hJnat
  have hXnat : 2 ^ (n + 1) - 2 ≤ 2 * 2 ^ n := by
    rw [pow_succ]
    omega
  have hX : X ≤ 2 * P := by
    dsimp [X, P]
    exact_mod_cast hXnat
  have hnmNat : n ≤ 4 * ((n - 1) / 2) := by omega
  have hnm : (n : ℝ) ≤ 4 * m := by
    dsimp [m]
    exact_mod_cast hnmNat
  have hnx : (n : ℝ) * X ≤ 8 * J := by
    calc
      (n : ℝ) * X ≤ (n : ℝ) * (2 * P) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      _ ≤ (4 * m) * (2 * P) :=
        mul_le_mul_of_nonneg_right hnm (by positivity)
      _ = 8 * (m * P) := by ring
      _ ≤ 8 * J := mul_le_mul_of_nonneg_left hJlower (by norm_num)
  have hratio : X / J ≤ 8 / (n : ℝ) := by
    rw [div_le_div_iff₀ hJpos hnpos]
    nlinarith
  calc
    repositoryCatalysisP (lambda * n) n * repositoryGatewayCoordinateCount n =
        34 * lambda * (n : ℝ) * (X / J) := by
      rw [repositoryCatalysisP, repositoryGatewayCoordinateCount_exact]
      simp only [X, J, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ 34 * lambda * (n : ℝ) * (8 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 272 * lambda := by field_simp; ring

/-- For every finite positive linear catalysis coefficient, the actual
repository RAF probability retains an eventual positive gateway-closed gap
and therefore cannot converge to one. -/
theorem linear_catalysis_actual_repository_raf_not_tendsto_one
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ¬ Tendsto
        (repositoryRAFBernoulliProbability (fun n => lambda * n))
        atTop (𝓝 1) := by
  let p : Nat → ℝ := fun n => repositoryCatalysisP (lambda * n) n
  let K : Nat → Nat := repositoryGatewayCoordinateCount
  let C : ℝ := 272 * lambda
  have hcount : Tendsto K atTop atTop := repositoryGatewayCoordinateCount_tendsto
  have hcountReal : Tendsto (fun n => (K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcount
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hC : ∀ᶠ n in atTop, C ≤ (K n : ℝ) :=
    hcountReal.eventually_ge_atTop C
  have hrate : ∀ᶠ n in atTop,
      0 ≤ 1 - C / (K n : ℝ) ∧ p n ≤ C / (K n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 3, hC] with n hn hCK
    have hKpos : (0 : ℝ) < K n := lt_of_lt_of_le hCpos hCK
    have hmass : p n * K n ≤ C := by
      simpa [p, K, C] using
        repository_linear_rate_mul_gatewayCoordinateCount_le
          (le_of_lt hlambda) hn
    constructor
    · rw [sub_nonneg, div_le_one hKpos]
      exact hCK
    · exact (le_div_iff₀ hKpos).2 hmass
  obtain ⟨delta, hdelta, hclosed⟩ :=
    RAF.Asymptotics.bernoulli_absent_eventually_pos p K C hcount hrate
  intro hraf
  have hrafLower : ∀ᶠ n in atTop,
      1 - delta / 2 < repositoryRAFBernoulliProbability
        (fun n => lambda * n) n :=
    (tendsto_order.1 hraf).1 (1 - delta / 2) (by linarith)
  have hbound : ∀ᶠ n in atTop,
      repositoryRAFBernoulliProbability (fun n => lambda * n) n +
        (1 - p n) ^ K n ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop 3, hrate] with n hn hr
    have hp0 : 0 ≤ p n := by
      dsimp [p]
      exact repositoryCatalysisP_nonneg (by positivity) n
    have hp1 : p n ≤ 1 := hr.2.trans (by linarith [hr.1])
    have hcontain := Source.repositoryRAFBernoulliProbability_le_gateway
      hp0 hp1 (by omega : 1 ≤ n)
    rw [repositoryGatewayOpenProbability, RAF.Corrected.atLeastOneProbability,
      RAF.Probability.allAbsentProbability_eq_pow] at hcontain
    change repositoryRAFBernoulliProbability (fun n => lambda * n) n ≤
      1 - (1 - p n) ^ K n at hcontain
    linarith
  have hfalse : ∀ᶠ _n : Nat in atTop, False := by
    filter_upwards [hrafLower, hclosed, hbound] with n hr hc hb
    linarith
  exact (Filter.Eventually.exists hfalse).elim (fun _ h => h)

end OverlapCorrectedRAF.Asymptotic
