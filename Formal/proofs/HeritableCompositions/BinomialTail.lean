import proofs.HeritableCompositions.BinomialMoment

namespace HeritableCompositions

theorem finite_exp_markov {ι : Type*} (S : Finset ι) (w X : ι → ℝ) (d t : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (ht : 0 ≤ t) :
    Real.exp (t*d)*(∑ i ∈ S, if d ≤ X i then w i else 0) ≤
      ∑ i ∈ S, w i*Real.exp (t*X i) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : d ≤ X i
  · simp only [if_pos hx]
    have hh := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ht)) (hw i hi)
    nlinarith only [hh]
  · simp only [if_neg hx,mul_zero]
    exact mul_nonneg (hw i hi) (Real.exp_pos _).le

theorem finite_chernoff {ι : Type*} (S : Finset ι) (w X : ι → ℝ) (d t v : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (ht : 0 ≤ t)
    (hm : ∑ i ∈ S, w i*Real.exp (t*X i) ≤ Real.exp v) :
    (∑ i ∈ S, if d ≤ X i then w i else 0) ≤ Real.exp (v-t*d) := by
  have h := (finite_exp_markov S w X d t hw ht).trans hm
  have he : Real.exp (t*d)*Real.exp (v-t*d) = Real.exp v := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he] at h
  nlinarith only [h,Real.exp_pos (t*d)]

theorem fair_binomial_upper_tail (n : ℕ) (hn : 0 < n) (d : ℝ) (hd : 0 ≤ d) :
    (∑ k ∈ Finset.range (n+1), if d ≤ (k : ℝ)-(n : ℝ)/2 then fairBinomialWeight n k else 0) ≤
      Real.exp (-2*d^2/(n : ℝ)) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h := finite_chernoff (Finset.range (n+1)) (fairBinomialWeight n)
    (fun k => (k : ℝ)-(n : ℝ)/2) d (4*d/(n : ℝ)) ((n : ℝ)*(4*d/(n : ℝ))^2/8)
    (fun k _ => fairBinomialWeight_nonneg n k) (by positivity) (fair_binomial_subgaussian n _)
  convert h using 1
  congr 1
  field_simp
  ring

theorem fair_binomial_lower_tail (n : ℕ) (hn : 0 < n) (d : ℝ) (hd : 0 ≤ d) :
    (∑ k ∈ Finset.range (n+1), if d ≤ -((k : ℝ)-(n : ℝ)/2) then fairBinomialWeight n k else 0) ≤
      Real.exp (-2*d^2/(n : ℝ)) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (∑ k ∈ Finset.range (n+1), fairBinomialWeight n k*
      Real.exp ((4*d/(n : ℝ))*(-((k : ℝ)-(n : ℝ)/2)))) ≤
      Real.exp ((n : ℝ)*(4*d/(n : ℝ))^2/8) := by
    convert fair_binomial_subgaussian n (-(4*d/(n : ℝ))) using 1 <;> ring_nf
  have h := finite_chernoff (Finset.range (n+1)) (fairBinomialWeight n)
    (fun k => -((k : ℝ)-(n : ℝ)/2)) d (4*d/(n : ℝ)) ((n : ℝ)*(4*d/(n : ℝ))^2/8)
    (fun k _ => fairBinomialWeight_nonneg n k) (by positivity) hm
  convert h using 1
  congr 1
  field_simp
  ring

theorem fair_binomial_two_sided_tail (n : ℕ) (hn : 0 < n) (d : ℝ) (hd : 0 ≤ d) :
    (∑ k ∈ Finset.range (n+1), if d ≤ |(k : ℝ)-(n : ℝ)/2| then fairBinomialWeight n k else 0) ≤
      2*Real.exp (-2*d^2/(n : ℝ)) := by
  have hpoint (k : ℕ) :
      (if d ≤ |(k : ℝ)-(n : ℝ)/2| then fairBinomialWeight n k else 0) ≤
      (if d ≤ (k : ℝ)-(n : ℝ)/2 then fairBinomialWeight n k else 0)+
      (if d ≤ -((k : ℝ)-(n : ℝ)/2) then fairBinomialWeight n k else 0) := by
    have hw := fairBinomialWeight_nonneg n k
    split_ifs with habs hp hm hp hm
    all_goals try linarith only [hw]
    have ha : |(k : ℝ)-(n : ℝ)/2| < d := abs_lt.mpr ⟨by linarith,by linarith⟩
    linarith only [ha,habs]
  have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (n+1)) => hpoint k)
  rw [Finset.sum_add_distrib] at h
  linarith only [h,fair_binomial_upper_tail n hn d hd,fair_binomial_lower_tail n hn d hd]

end HeritableCompositions
