import proofs.HeritableCompositions.BinomialMoment

namespace HeritableCompositions

theorem fair_binomial_pmf_weight (n k : ℕ) (hk : k ≤ n) :
    (PMF.binomial (1/2) (by norm_num) n (Fin.ofNat (n+1) k)).toReal =
      fairBinomialWeight n k := by
  rw [← PMF.binomial_apply_of_le hk (by norm_num : (1/2 : NNReal) ≤ 1)]
  rw [ENNReal.toReal_ofReal (by norm_num)]
  norm_num
  unfold fairBinomialWeight
  have hs : (1/2 : ℝ)^k*(1/2 : ℝ)^(n-k) = (1/2 : ℝ)^n := by
    rw [← pow_add,show k+(n-k)=n by omega]
  calc
    (n.choose k : ℝ)*(1/2)^k*(1/2)^(n-k) = (n.choose k : ℝ)*((1/2)^k*(1/2)^(n-k)) := by ring
    _ = (n.choose k : ℝ)*(1/2)^n := by rw [hs]
    _ = _ := by rw [div_pow,one_pow]; ring

end HeritableCompositions
