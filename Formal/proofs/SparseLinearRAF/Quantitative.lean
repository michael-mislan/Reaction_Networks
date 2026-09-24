import proofs.SparseLinearRAF.LiteratureResolution

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete HordijkSteelThreshold Filter Topology

theorem scaled_activity_tendsto_zero {lambda : ℝ} (hl : 0 ≤ lambda) :
    Tendsto (fun n : Nat => (n:ℝ)*(activityParameter n lambda : ℝ)) atTop (𝓝 0) := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 3
    (by norm_num : (1:ℝ)<2)).const_mul lambda
  apply squeeze_zero' (Eventually.of_forall (fun n => by
    have := (activityParameter n lambda).2.1; positivity)) ?_ (by simpa using ht)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hh := mul_le_mul_of_nonneg_left (activity_le_polynomial_exp hl hn) (Nat.cast_nonneg n : (0:ℝ)≤n)
  convert hh using 1
  ring

noncomputable def rankRateConstant (t k : Nat) (lambda : ℝ) : ℝ :=
  (shallowBound (Fintype.card (Molecule t)) t (k+1):ℝ) +
  (prefixBound (Fintype.card (Molecule t)) t 0 (k+1):ℝ)*(k:ℝ)^(k+1)*(lambda+1)^k

theorem fixed_rank_scaled_bound (t k : Nat) (hk : 0 < k) {lambda : ℝ} (hl : 0 ≤ lambda) :
    ∀ᶠ n : Nat in atTop, (n:ℝ)*coverRankProbability n t k lambda ≤ rankRateConstant t k lambda := by
  have hmass := (rawCatalysisP_mul_card_molecule_tendsto lambda).eventually_lt_const
    (by linarith : lambda < lambda+1)
  filter_upwards [hmass, (scaled_activity_tendsto_zero hl).eventually_lt_const
    (by norm_num : (0:ℝ)<1), eventually_ge_atTop 1] with n hmass hact hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp0 := (activityParameter n lambda).2.1
  have hq0 := (channelParameter n).2.1
  have hmass0 : 0 ≤ rawCatalysisP n lambda * (Fintype.card (Molecule n):ℝ) := by
    unfold rawCatalysisP; positivity
  have hpk := pow_le_pow_left₀ hp0 (activity_le_raw hl n) k
  have hb := mul_le_mul_of_nonneg_left (coverRankProbability_bound n t k (k+1) hk lambda)
    (Nat.cast_nonneg n : (0:ℝ)≤n)
  have hm : (n:ℝ)*(Fintype.card (Molecule n):ℝ)^k*(activityParameter n lambda : ℝ)^k*
      (channelParameter n : ℝ)^(k+1) ≤ (lambda+1)^k := by
    calc
      _ ≤ (n:ℝ)*(Fintype.card (Molecule n):ℝ)^k*(rawActivity n lambda)^k*
          (channelParameter n : ℝ)^(k+1) := by gcongr
      _ = (rawCatalysisP n lambda*(Fintype.card (Molecule n):ℝ))^k := by
        rw [rawActivity_eq]
        dsimp [channelParameter]
        rw [mul_pow, mul_pow, pow_succ, inv_pow]
        field_simp
      _ ≤ _ := pow_le_pow_left₀ hmass0 hmass.le k
  let H : ℝ := shallowBound (Fintype.card (Molecule t)) t (k+1)
  let B : ℝ := (prefixBound (Fintype.card (Molecule t)) t 0 (k+1):ℝ)*(k:ℝ)^(k+1)
  have h1 := mul_le_mul_of_nonneg_left hact.le (show 0 ≤ H by dsimp [H]; positivity)
  have h2 := mul_le_mul_of_nonneg_left hm (show 0 ≤ B by dsimp [B]; positivity)
  have hsum := add_le_add h1 h2
  apply hb.trans
  convert hsum using 1 <;> dsimp [H,B,rankRateConstant] <;> ring

theorem bounded_rank_scaled_bound (t K : Nat) {lambda : ℝ} (hl : 0 ≤ lambda) :
    ∀ᶠ n : Nat in atTop, (n:ℝ)*boundedCoverRankProbability n t K lambda ≤
      ∑ k ∈ Finset.range K, rankRateConstant t (k+1) lambda := by
  have hh : ∀ᶠ n : Nat in atTop, ∀ k ∈ Finset.range K,
      (n:ℝ)*coverRankProbability n t (k+1) lambda ≤ rankRateConstant t (k+1) lambda :=
    (Finset.eventually_all _).mpr (fun k _ => fixed_rank_scaled_bound t (k+1) (by omega) hl)
  filter_upwards [hh] with n hn
  apply (mul_le_mul_of_nonneg_left (boundedCoverRankProbability_le n t K lambda)
    (Nat.cast_nonneg n : (0:ℝ)≤n)).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hn

/-- An explicit inverse-linear term and an exponentially small tail. -/
theorem linear_raf_quantitative_bound (t C : Nat) {lambda : ℝ} (hl : 0 ≤ lambda) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n in atTop,
      linearRAFProbability n t C lambda ≤ A/(n:ℝ) +
        (C:ℝ)*(n:ℝ)*((Fintype.card (Molecule t):ℝ)+3*C*n)*(3/4:ℝ)^n := by
  obtain ⟨K,hK⟩ := large_rank_uniform_estimate t C hl
  let A : ℝ := (Fintype.card (Molecule t):ℝ) +
    ∑ k ∈ Finset.range K, rankRateConstant t (k+1) lambda
  refine ⟨A, ?_, ?_⟩
  · dsimp [A,rankRateConstant]
    positivity
  filter_upwards [hK,bounded_rank_scaled_bound t K hl,
    (scaled_activity_tendsto_zero hl).eventually_lt_const (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop 1] with n hn hr ha hn1
  have hnpos : (0:ℝ)<n := by exact_mod_cast hn1
  have hb : (Fintype.card (Molecule t):ℝ)*(activityParameter n lambda : ℝ) +
      boundedCoverRankProbability n t K lambda ≤ A/(n:ℝ) := by
    apply (le_div_iff₀ hnpos).mpr
    have hh := mul_le_mul_of_nonneg_left ha.le
      (show (0:ℝ)≤Fintype.card (Molecule t) by positivity)
    dsimp [A]
    nlinarith
  have h := linearRAFProbability_bound n t C K lambda ((3/4:ℝ)^n) (by positivity) hn
  push_cast at h
  exact h.trans (add_le_add hb le_rfl)

end SparseLinearRAF
