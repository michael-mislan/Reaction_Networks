import proofs.ResourceLimitedCompetition.SharperError
namespace ResourceLimitedCompetition
open Filter
open scoped Topology

theorem chemical_joint_envelope (N : ℕ) (M γ : ℝ) (hM : 0 ≤ M) (hγ : 0 < γ) (hγmax : γ ≤ 1) :
    chemicalRawError N M (8/γ) ≤
      34*(M/γ)*((N : ℝ)+1)*Real.exp (-(3/2)*chemicalScale N) := by
  have hu : chemicalScale N ≤ (N : ℝ) := by
    unfold chemicalScale FiniteCopy.localAlpha HeritableCompositions.innerEnergy HeritableCompositions.outerEnergy
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith only [hn]
  have hcoef : 32+(8/γ)*chemicalScale N/42 ≤ 34*((N : ℝ)+1)/γ := by
    apply (le_div_iff₀ hγ).mpr
    have hi : (32+(8/γ)*chemicalScale N/42)*γ=32*γ+(4/21)*chemicalScale N := by
      field_simp
      ring
    rw [hi]
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith only [hu,hγmax,hn]
  have hs := chemical_raw_sharp N M (8/γ) hM (by positivity)
  have hm := mul_le_mul_of_nonneg_left hcoef hM
  have he := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-(3/2)*chemicalScale N)).le
  apply hs.trans
  convert he using 1
  ring

theorem exponential_accuracy (K a ε : ℝ) (hK : 0 < K) (hε : 0 < ε)
    (ha : Real.log (K/ε) ≤ a) : K*Real.exp (-a) ≤ ε := by
  have h := Real.exp_le_exp.mpr (neg_le_neg ha)
  have hi : Real.exp (-Real.log (K/ε))=ε/K := by
    rw [Real.exp_neg,Real.exp_log (div_pos hK hε)]
    field_simp
  rw [hi] at h
  have hm := mul_le_mul_of_nonneg_left h hK.le
  have hc : K*(ε/K)=ε := by field_simp
  simpa only [hc] using hm

theorem three_tail_accuracy (K a b d ε : ℝ) (hK : 0 < K) (hε : 0 < ε)
    (ha : Real.log (3*K/ε) ≤ a) (hb : Real.log (3/ε) ≤ b) (hd : Real.log (3/ε) ≤ d) :
    K*Real.exp (-a)+Real.exp (-b)+Real.exp (-d) ≤ ε := by
  have hc : K/(ε/3)=3*K/ε := by ring
  have h1 := exponential_accuracy K a (ε/3) hK (by positivity) (by simpa only [hc] using ha)
  have hc1 : (1 : ℝ)/(ε/3)=3/ε := by ring
  have h2 := exponential_accuracy 1 b (ε/3) (by norm_num) (by positivity) (by simpa only [hc1] using hb)
  have h3 := exponential_accuracy 1 d (ε/3) (by norm_num) (by positivity) (by simpa only [hc1] using hd)
  norm_num only [one_mul] at h2 h3
  linarith only [h1,h2,h3]

theorem joint_scaling_decay (M γ : ℕ → ℝ) (hM : ∀ N, 0 < M N) (hγ : ∀ N, 0 < γ N)
    (h : Tendsto (fun N => Real.log (M N)+Real.log (1/γ N)+Real.log ((N : ℝ)+1)-
      (3/2)*chemicalScale N) atTop atBot) :
    Tendsto (fun N => M N/γ N*((N : ℝ)+1)*Real.exp (-(3/2)*chemicalScale N)) atTop (𝓝 0) := by
  simp only [neg_mul]
  apply exponential_log_budget (fun N => M N/γ N*((N : ℝ)+1)) (fun N => (3/2)*chemicalScale N)
    (fun N => mul_pos (div_pos (hM N) (hγ N)) (by positivity))
  convert h using 1
  funext N
  rw [Real.log_mul (ne_of_gt (div_pos (hM N) (hγ N))) (by positivity),
    Real.log_div (ne_of_gt (hM N)) (ne_of_gt (hγ N)),
    Real.log_div (by norm_num) (ne_of_gt (hγ N)),Real.log_one]
  ring

end ResourceLimitedCompetition
