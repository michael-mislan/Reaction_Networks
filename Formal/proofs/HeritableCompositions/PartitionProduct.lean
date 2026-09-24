import proofs.HeritableCompositions.BinomialTail
import proofs.HeritableCompositions.BinomialLaw

namespace HeritableCompositions
open Fintype

theorem product_weight_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Finset ℕ)
    (w : ι → ℕ → ℝ) (hw : ∀ i, ∑ k ∈ S i, w i k = 1) :
    ∑ d ∈ piFinset S, ∏ i, w i (d i) = 1 := by
  rw [← Finset.prod_univ_sum]
  simp only [hw,Finset.prod_const_one]

theorem product_weight_marginal {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Finset ℕ)
    (w : ι → ℕ → ℝ) (hw : ∀ i, ∑ k ∈ S i, w i k = 1) (j : ι) (g : ℕ → ℝ) :
    ∑ d ∈ piFinset S, (∏ i, w i (d i))*g (d j) = ∑ k ∈ S j, w j k*g k := by
  classical
  have hp (d : ι → ℕ) : (∏ i, w i (d i))*g (d j) =
      ∏ i, w i (d i)*(if i=j then g (d i) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [hp]
  rw [← Finset.prod_univ_sum S (fun i k => w i k*(if i=j then g k else 1))]
  have hs (i : ι) : (∑ k ∈ S i, w i k*(if i=j then g k else 1)) =
      if i=j then (∑ k ∈ S j, w j k*g k) else 1 := by
    by_cases hi : i=j
    · subst i
      simp
    · simp [hi,hw i]
  simp_rw [hs]
  simp

noncomputable def daughterDraws (n : Fin 4 → ℕ) : Finset (Fin 4 → ℕ) :=
  piFinset (fun i => Finset.range (n i+1))

noncomputable def daughterWeight (n d : Fin 4 → ℕ) : ℝ :=
  ∏ i, fairBinomialWeight (n i) (d i)

theorem daughterWeight_nonneg (n d : Fin 4 → ℕ) : 0 ≤ daughterWeight n d :=
  Finset.prod_nonneg (fun i _ => fairBinomialWeight_nonneg (n i) (d i))

theorem daughterWeight_sum (n : Fin 4 → ℕ) :
    ∑ d ∈ daughterDraws n, daughterWeight n d = 1 :=
  product_weight_sum _ _ (fun i => fair_binomial_sum (n i))

theorem daughterWeight_marginal (n : Fin 4 → ℕ) (j : Fin 4) (g : ℕ → ℝ) :
    ∑ d ∈ daughterDraws n, daughterWeight n d*g (d j) =
      ∑ k ∈ Finset.range (n j+1), fairBinomialWeight (n j) k*g k :=
  product_weight_marginal _ _ (fun i => fair_binomial_sum (n i)) j g

end HeritableCompositions
